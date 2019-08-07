// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Scored Pool Module
//!
//! The module maintains a membership pool -- the pool requires type
//! `CandidateDeposit: Get<BalanceOf<Self>>` deposit to place into
//! (and returns it when withdrawn).
//!
//! Allows a configurable `type ScoreOrigin: EnsureOrigin` origin type
//! to set a score to a candidate in the pool.
//!
//! Every `type Period: Get<Self::BlockNumber>` blocks, it fills the members
//! from the highest scoring members in the pool (including those from the
//! previous membership) and calls `T::MembersChanged::change_members` accordingly.
//!
//! An additional configurable `type KickOrigin: EnsureOrigin` origin should be
//! able to remove any current member and place the next highest scoring candidate
//! in the membership
//!
//! It should be possible to withdraw your candidacy/resign your membership at
//! any time; if you're currently a member, it will result in your removal from
//! the set and replacement by the next highest scoring candidate in the pool.
//! the pool and the set are two different groups
//! membership of the pool is essentially a superset of the members of the set.
//!
//! you just deposit some DOTs (given by type `CandidateDeposit: Get<BalanceOf<Self>>`)
//! to go into the pool you get them back when you withdraw from the pool
//! there is no fixed constant that represents the maximum pool size. anyone can
//! join if they are willing to lock up the deposit.
//! the Set, though, is a fixed size.
//! `MemberCount: u32` is the size. it's a storage item
//! the Set should be reset to the `MemberCount` members of the pool with the highest
//! scores once every `Period`.
//!
//! if someone leaves (or is kicked), then the highest member of the pool that is
//! not currently in the set should be placed in the set instead.
//! whenever the membership of the set changes, use `T::MembersChanged::change_members`
//! to publish it.
//! you can put in a root-dispatchable call to change MemberCount
//!
//! - [`scored_pool::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `is_online_in_current_era` - True if the validator sent a heartbeat in the current era.
//! - `is_online_in_current_session` - True if the validator sent a heartbeat in the current session.
//!
//! ## Usage
//!
//! ```
//! use srml_support::{decl_module, dispatch::Result};
//! use system::ensure_signed;
//! use srml_im_online::{self as im_online};
//!
//! pub trait Trait: im_online::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn is_online(origin, authority_id: T::AuthorityId) -> Result {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _is_online = <im_online::Module<T>>::is_online_in_current_era(&authority_id);
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```
//!
//! ## Dependencies
//!
//! This module depends on the [Session module](../srml_session/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode};
use sr_std::prelude::*;
use sr_std::prelude::Ordering;
use srml_support::{
	StorageValue, decl_module, decl_storage, decl_event,
	traits::{ChangeMembers, Currency, Get, ReservableCurrency},
};
use system::{self, ensure_root, ensure_signed};
use sr_primitives::{
	traits::{EnsureOrigin, SimpleArithmetic, MaybeSerializeDebug},
};

type BalanceOf<T, I> = <<T as Trait<I>>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
//type PoolT = Vec<(T::AccountId, Option<T::Score>)>;

//pub trait Trait<I=DefaultInstance>: system::Trait {
pub trait Trait<I=DefaultInstance>: system::Trait {
	/// The staking balance.
	type Currency: Currency<Self::AccountId> + ReservableCurrency<Self::AccountId>;

	/// The score.
	type Score: SimpleArithmetic + Clone + Encode + Decode + MaybeSerializeDebug; // TODO why debug?

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;

	// The deposit to place into (and return when withdrawn).
	type CandidateDeposit: Get<BalanceOf<Self, I>>;

	/// Every `` blocks, it fills the members from the highest scoring members in
	/// the pool (including those from the previous membership).
	type Period: Get<Self::BlockNumber>;

	/// The receiver of the signal for when the membership has been initialized. This happens pre-
	/// genesis and will usually be the same as `MembershipChanged`. If you need to do something
	/// different on initialization, then you can change this accordingly.
	type MembershipInitialized: ChangeMembers<Self::AccountId>;

	/// The receiver of the signal for when the members have changed.
	type MembershipChanged: ChangeMembers<Self::AccountId>;

	/// Allows a configurable origin type to set a score to a candidate in the pool.
	type ScoreOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for adding a member (though can always be Root).
	type AddOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for removing a member (though can always be Root).
	/// Configurable origin which enables removing any current member and
	/// places the next highest scoring candidate in the membership.
	/// Required origin for removing an enitityt from the membership.
	type RemoveOrigin: EnsureOrigin<Self::Origin>;
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Membership {
		/// The current pool of candidates, stored as an ordered Vec
		/// (ordered by score).
		Pool get(pool) config(): Vec<(T::AccountId, Option<T::Score>)>; //PoolT;
		//Pool get(pool): map T::AccountId => Option<T::Score>;

		/// The current membership, stored as an ordered Vec.
		Members get(members): Vec<T::AccountId>;

		/// Size of the set.
		MemberCount get(member_count) config(): u32;
	}
	add_extra_genesis {
		config(members): Vec<T::AccountId>;
		config(phantom): sr_std::marker::PhantomData<I>;
		build(|
			storage: &mut (sr_primitives::StorageOverlay, sr_primitives::ChildrenStorageOverlay),
			config: &GenesisConfig<T, I>
		| {
			sr_io::with_storage(storage, || {
				let pool = config.pool.clone();
				<Pool<T, I>>::put(&pool);

				<Module<T, I>>::sort_pool_no();
				<Module<T, I>>::refresh_members();
				/*
				//let mut pool: Pool<T, I> = <Pool<T, I>>::get();
				let mut pool = <Pool<T, I>>::get();
				<Module<T, I>>::sort_pool(&mut pool);
				//<Module<T, I>>::sort_pool(&mut pool as Pool<T, I>);
				<Pool<T, I>>::put(&pool);
				*/

				// fetch `MemberCount` members from pool and put them into members
				/*
				<Module<T, I>>::refresh_members(&mut members);
				*/

				//members.sort(); TODO sort_by

				let members = <Members<T, I>>::get();
				T::MembershipInitialized::set_members_sorted(&members[..], &[]);
				//<Members<T, I>>::put(&members);
			});
		})
	}
}

decl_event!(
	pub enum Event<T, I=DefaultInstance> where
		<T as system::Trait>::AccountId,
	{
		/// The given member was added; see the transaction for who.
		MemberAdded,
		/// The given member was removed; see the transaction for who.
		MemberRemoved,
		/// TODO
		CandidateAdded,
		/// TODO
		CandidateWithdrew,
		/// TODO
		CandidateKicked,
		/// Phantom member, never used.
		Dummy(sr_std::marker::PhantomData<(AccountId, I)>),
	}
);

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance>
		for enum Call
		where origin: T::Origin
	{
		fn deposit_event<T, I>() = default;

		// the Set should be reset to the `MemberCount` members of the pool with the highest
		// scores once every `Period`.
		fn on_initialize(n: T::BlockNumber) {
			if n == T::Period::get() {
				<Module<T, I>>::refresh_members();
			}
		}

		/// Add `origin` to the pool of candidates.
		fn issue_candidacy(origin) {
			let who = ensure_signed(origin)?;

			let mut pool = <Pool<T, I>>::get();
			pool.push((who.clone(), None));

			T::Currency::reserve(&who, T::CandidateDeposit::get())
				.map_err(|_| "candidate's balance too low")?;

			<Pool<T, I>>::put(&pool);

			Self::deposit_event(RawEvent::CandidateAdded);
		}

		// if someone leaves (or is kicked), then the highest member of the pool that is
		// not currently in the set should be placed in the set instead.
		// any time; if you're currently a member, it will result in your removal from
		// the set and replacement by the next highest scoring candidate in the pool.
		fn withdraw_candidacy(origin) {
			let who = ensure_signed(origin)?;
			Self::remove_member(who)?;
			Self::deposit_event(RawEvent::CandidateWithdrew);
		}

		/// Kick a member `who` from the set.
		///
		/// May only be called from `RemoveOrigin` or root.
		fn kick(origin, who: T::AccountId) {
			T::RemoveOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			Self::remove_member(who)?;
			Self::deposit_event(RawEvent::CandidateKicked);
		}

		/// Score a member `who` with `score`.
		///
		/// May only be called from `ScoreOrigin` or root.
		fn score(origin, who: T::AccountId, score: T::Score) {
			T::ScoreOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			let mut pool = <Pool<T, I>>::get();
			let location = Self::find_in_pool(&who)?;
			pool.insert(location, (who.clone(), Some(score.clone())));
			<Pool<T, I>>::put(&pool);

			Self::sort_pool(&mut pool);
		}

		/// Root-dispatchable call to change MemberCount
		fn change_member_count(origin, count: u32) {
			ensure_root(origin)?;
			<MemberCount<I>>::put(&count);
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {

	// fetch `MemberCount` members from pool and put them into members
	fn refresh_members() {
		let count = <MemberCount<I>>::get();

		let pool = <Pool<T, I>>::get();
		let new_members: Vec<T::AccountId> = pool
			.into_iter()
			.take(count as usize)
			.map(|(account_id, _)| account_id)
			.collect();
		<Members<T, I>>::put(&new_members);
	}

	fn sort_pool_no() {
		let mut pool = <Pool<T, I>>::get();
		<Module<T, I>>::sort_pool(&mut pool);
	}

	fn sort_pool(pool: &mut Vec<(T::AccountId, Option<T::Score>)>) {
		pool.sort_by(|(_, maybe_score_a), (_, maybe_score_b)| {
			match maybe_score_a {
				Some(score_a) => {
					match maybe_score_b {
						Some(score_b) => score_a.cmp(score_b),
						None => Ordering::Greater, // any score is always greater than None
					}
				},
				None => {
					match maybe_score_b {
						Some(_score_b) => Ordering::Less, // any score is always greater than None
						None => Ordering::Equal,
					}
				}
			}
		});
	}

	// return the next highest scoring one which is not in the set
	/*
	fn next_highest_scoring(location: usize) -> Option<usize> {
		let pool = <Pool<T, I>>::get();
		if location >= pool.len() - 1 {
			return None;
		}

		Some(location + 1)
	}
	*/

	fn find_in_pool(who: &T::AccountId) -> Result<usize, &'static str> {
		let pool = <Pool<T, I>>::get();
		pool.binary_search_by(|item| item.0.cmp(who))
			.ok().ok_or("not a member")
	}

	fn remove_member(remove: T::AccountId) -> Result<(), &'static str> {
		// remove from pool
		let mut pool = <Pool<T, I>>::get();
		let location = Self::find_in_pool(&remove)?;

		// remove from set, if it was in there
		let mut members = <Members<T, I>>::get();
		let maybe_location = members.binary_search(&remove); //.ok().ok_or("not a member")?;
		if let Ok(location) = maybe_location {
			let (who, _score) = pool.get(location).ok_or("no member at location")?;
			// is there a next, highest-scoring one?

			let add = {
				if location >= pool.len() - 1 {
					None
				} else {
					Some(location + 1)
				}
			};

			//let add = Self::next_highest_scoring(location, who, score);
			match add {
				Some(location_next) => {
					// if yes replace
					let (add, _score) = &pool[location_next];
					members[location] = add.clone();
					let _location = members.binary_search(&add)
						.err().ok_or("already a member")?;
					members.sort();
					<Members<T, I>>::put(&members);

					T::MembershipChanged::change_members_sorted(
						&[add.clone()],
						&[remove],
						&members[..],
					);
				}
				None => {
					// else just remove from set
					let mut members = <Members<T, I>>::get();
					let location = members.binary_search(&remove).ok().ok_or("not a member")?;
					members.remove(location);
					<Members<T, I>>::put(&members);

					T::MembershipChanged::change_members_sorted(&[], &[who.clone()], &members[..]);
				}
			}
		}

		pool.remove(location);
		<Pool<T, I>>::put(&pool);

		Self::deposit_event(RawEvent::MemberRemoved);
		Ok(())
	}

}

#[cfg(test)]
mod tests {
	use super::*;

	use std::cell::RefCell;
	use srml_support::{assert_ok, assert_noop, impl_outer_origin, parameter_types};
	use sr_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
	use sr_primitives::{
		Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header
	};
	use system::EnsureSignedBy;

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	/*
	type Balance = u64;

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			balances::Balances,
			scored_pool::ScoredPool,
		}
	}
	*/

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const CandidateDeposit: u64 = 25;
		pub const Period: u64 = 4;

		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();

		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
		pub const TransactionBaseFee: u64 = 0;
		pub const TransactionByteFee: u64 = 0;
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
	}

	impl balances::Trait for Test {
		type Balance = u64;
		type OnFreeBalanceZero = ();
		type OnNewAccount = ();
		type Event = ();
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
		type TransactionBaseFee = TransactionBaseFee;
		type TransactionByteFee = TransactionByteFee;
		type WeightToFee = ();
	}

	parameter_types! {
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
		pub const Three: u64 = 3;
		pub const Four: u64 = 4;
		pub const Five: u64 = 5;
	}

	thread_local! {
		static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
	}

	pub struct TestChangeMembers;
	impl ChangeMembers<u64> for TestChangeMembers {
		fn change_members_sorted(incoming: &[u64], outgoing: &[u64], new: &[u64]) {
			let mut old_plus_incoming = MEMBERS.with(|m| m.borrow().to_vec());
			old_plus_incoming.extend_from_slice(incoming);
			old_plus_incoming.sort();
			let mut new_plus_outgoing = new.to_vec();
			new_plus_outgoing.extend_from_slice(outgoing);
			new_plus_outgoing.sort();
			assert_eq!(old_plus_incoming, new_plus_outgoing);

			MEMBERS.with(|m| *m.borrow_mut() = new.to_vec());
		}
	}

	impl Trait for Test {
		type Event = ();
		type AddOrigin = EnsureSignedBy<One, u64>;
		type RemoveOrigin = EnsureSignedBy<Two, u64>;
		type MembershipInitialized = TestChangeMembers;
		type MembershipChanged = TestChangeMembers;

		type Currency = balances::Module<Self>;
		//type Currency = ();
		type CandidateDeposit = CandidateDeposit;
		type Period = Period;
		type Score = u64;
		type ScoreOrigin = EnsureSignedBy<Three, u64>;
	}

	type Membership = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sr_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		GenesisConfig::<Test>{
			pool: vec![
				(10, Some(1)),
				(20, Some(2)),
				(21, Some(2)),
				(30, Some(3)),
			],
			member_count: 2,
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn query_membership_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Membership::members(), vec![10, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), vec![10, 20, 30]);
		});
	}

	/*
	#[test]
	fn add_member_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Membership::add_member(Origin::signed(5), 15), "bad origin");
			assert_noop!(Membership::add_member(Origin::signed(1), 10), "already a member");
			assert_ok!(Membership::add_member(Origin::signed(1), 15));
			assert_eq!(Membership::members(), vec![10, 15, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn remove_member_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Membership::remove_member(Origin::signed(5), 20), "bad origin");
			assert_noop!(Membership::remove_member(Origin::signed(2), 15), "not a member");
			assert_ok!(Membership::remove_member(Origin::signed(2), 20));
			assert_eq!(Membership::members(), vec![10, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}
	*/
}

// TODO test for this:
//   when removing, no higher scoring available, only ones with None score.
//   one of those should be used then i guess?
