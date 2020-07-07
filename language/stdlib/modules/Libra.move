address 0x1 {


module Libra {
    use 0x1::CoreAddresses;
    use 0x1::RegisteredCurrencies::{Self, RegistrationCapability};
    use 0x1::Signer;
    use 0x1::Vector;
    use 0x1::LibraTimestamp;







    resource struct Libra<CoinType> {
        /// The value of this coin in the base units for `CoinType`
        value: u64
    }





     /// ## Conservation of currency

     spec module {
        /// Maintain a spec variable representing the sum of
        /// all coins of a currency type.
        global sum_of_coin_values<CoinType>: num;
    }











    /// Account for updating `sum_of_coin_values` when a `Libra`
    /// is packed or unpacked.
    spec struct Libra {
        invariant pack sum_of_coin_values<CoinType>
                     = sum_of_coin_values<CoinType> + value;
        invariant unpack sum_of_coin_values<CoinType>
                       = sum_of_coin_values<CoinType> - value;
    }








    spec schema TotalValueRemainsSame<CoinType> {
        /// The total amount of currency stays constant.
        ensures sum_of_coin_values<CoinType>
            == old(sum_of_coin_values<CoinType>);
    }











    spec module {
        /// Only mint function can change the
        /// total amount of currency.
        apply TotalValueRemainsSame<CoinType> to *<CoinType>
            except mint<CoinType>;
    }









/// Burns the coins currently held in the `preburn`.
public fun burn<CoinType>(
    preburn: &mut Preburn<CoinType>,
)  {
    // Unpack the Libra coin and destroy it.
    let Libra { value } = Vector::remove(&mut preburn.requests, 0);
    let _ = value;
}





/// Mints `amount` coins.
public fun mint<CoinType>(value: u64): Libra<CoinType> {
    // Pack a Libra coin and return it.
    Libra<CoinType> { value }
}


    resource struct RegisterNewCurrency {}

    /// The `MintCapability` resource defines a capability to allow minting
    /// of coins of `CoinType` currency by the holder of this capability.
    /// This capability is held only either by the `CoreAddresses::TREASURY_COMPLIANCE_ADDRESS()` account or the
    /// `0x1::LBR` module (and `CoreAddresses::LIBRA_ROOT_ADDRESS()` in testnet).
    ///
    /// > TODO(wrwg): what does it mean that a capability is held by a module? Consider to remove?
    resource struct MintCapability<CoinType> { }

    /// The `BurnCapability` resource defines a capability to allow coins
    /// of `CoinType` currency to be burned by the holder of the
    /// and the `0x1::LBR` module (and `CoreAddresses::LIBRA_ROOT_ADDRESS()` in testnet).
    resource struct BurnCapability<CoinType> { }

    /// The `CurrencyRegistrationCapability` is a singleton resource
    /// published under the `CoreAddresses::LIBRA_ROOT_ADDRESS()` and grants
    /// the capability to the `0x1::Libra` module to add currencies to the
    /// `0x1::RegisteredCurrencies` on-chain config.
    resource struct CurrencyRegistrationCapability {
        /// A capability to allow updating the set of registered currencies on-chain.
        cap: RegistrationCapability,
    }

    resource struct Preburn<CoinType> {
        /// The queue of pending burn requests
        requests: vector<Libra<CoinType>>,
    }

    /// The `CurrencyInfo<CoinType>` resource stores the various
    /// pieces of information needed for a currency (`CoinType`) that is
    /// registered on-chain. This resource _must_ be published under the
    /// address given by `CoreAddresses::CURRENCY_INFO_ADDRESS()` in order for the registration of
    /// `CoinType` as a recognized currency on-chain to be successful. At
    /// the time of registration the `MintCapability<CoinType>` and
    /// `BurnCapability<CoinType>` capabilities are returned to the caller.
    /// Unless they are specified otherwise the fields in this resource are immutable.
    resource struct CurrencyInfo<CoinType> {
        /// The total value for the currency represented by `CoinType`. Mutable.
        total_value: u128,
        /// Value of funds that are in the process of being burned.  Mutable.
        preburn_value: u64,
        /// The (rough) exchange rate from `CoinType` to `LBR`. Mutable.
        // to_lbr_exchange_rate: FixedPoint32,
        /// Holds whether or not this currency is synthetic (contributes to the
        /// off-chain reserve) or not. An example of such a synthetic
        ///currency would be the LBR.
        is_synthetic: bool,
        /// The scaling factor for the coin (i.e. the amount to multiply by
        /// to get to the human-readable representation for this currency).
        /// e.g. 10^6 for `Coin1`
        ///
        /// > TODO(wrwg): should the above be "to divide by"?
        scaling_factor: u64,
        /// The smallest fractional part (number of decimal places) to be
        /// used in the human-readable representation for the currency (e.g.
        /// 10^2 for `Coin1` cents)
        fractional_part: u64,
        /// The code symbol for this `CoinType`. ASCII encoded.
        /// e.g. for "LBR" this is x"4C4252". No character limit.
        currency_code: vector<u8>,
        /// We may want to disable the ability to mint further coins of a
        /// currency while that currency is still around. This allows us to
        /// keep the currency in circulation while disallowing further
        /// creation of coins in the `CoinType` currency. Mutable.
        can_mint: bool,
    }

    ///////////////////////////////////////////////////////////////////////////
    // Initialization and granting of privileges
    ///////////////////////////////////////////////////////////////////////////

    /// Grants the `RegisterNewCurrency` privilege to
    /// the calling account as long as it has the correct role (TC).
    /// Aborts if `account` does not have a `RoleId` that corresponds with
    /// the treacury compliance role.
    // public fun grant_privileges(account: &signer) {
    // }

    /// Initialization of the `Libra` module; initializes the set of
    /// registered currencies in the `0x1::RegisteredCurrencies` on-chain
    /// config, and publishes the `CurrencyRegistrationCapability` under the
    /// `CoreAddresses::LIBRA_ROOT_ADDRESS()`. This can only be called from genesis.
    public fun initialize(
        config_account: &signer,
    ) {
        LibraTimestamp::assert_is_genesis();
        // Operational constraint
        assert(
            Signer::address_of(config_account) == CoreAddresses::LIBRA_ROOT_ADDRESS(),
            0
        );
        let cap = RegisteredCurrencies::initialize(config_account);
        move_to(config_account, CurrencyRegistrationCapability{ cap })
    }





    /// Create a new `Libra<CoinType>` with a value of `0`. Anyone can call
    /// this and it will be successful as long as `CoinType` is a registered currency.
    public fun zero<CoinType>(): Libra<CoinType> {
        assert_is_currency<CoinType>();
        Libra<CoinType> { value: 0 }
    }

    /// Returns the `value` of the passed in `coin`. The value is
    /// represented in the base units for the currency represented by
    /// `CoinType`.
    public fun value<CoinType>(coin: &Libra<CoinType>): u64 {
        coin.value
    }

    /// Withdraw `amount` from the passed-in `coin`, where the original coin is modified in place.
    /// After this function is executed, the original `coin` will have
    /// `value = original_value - amount`, and the new coin will have a `value = amount`.
    /// Calls will abort if the passed-in `amount` is greater than the
    /// value of the passed-in `coin`.
    public fun withdraw<CoinType>(coin: &mut Libra<CoinType>, amount: u64): Libra<CoinType> {
        // Check that `amount` is less than the coin's value
        assert(coin.value >= amount, 10);
        coin.value = coin.value - amount;
        Libra { value: amount }
    }
    spec fun withdraw {
        aborts_if coin.value < amount;
        ensures coin.value == old(coin.value) - amount;
        ensures result.value == amount;
    }

    /// "Merges" the two coins.
    /// The coin passed in by reference will have a value equal to the sum of the two coins
    /// The `check` coin is consumed in the process



    public fun deposit<CoinType>(
        coin: &mut Libra<CoinType>, check: Libra<CoinType>
    ) {
        let Libra { value } = check;
        coin.value = coin.value + value;
    }

    /// Returns `true` if the type `CoinType` is a registered currency.
    /// Returns `false` otherwise.
    public fun is_currency<CoinType>(): bool {
        exists<CurrencyInfo<CoinType>>(CoreAddresses::CURRENCY_INFO_ADDRESS())
    }

    ///////////////////////////////////////////////////////////////////////////
    // Helper functions
    ///////////////////////////////////////////////////////////////////////////

    /// Asserts that `CoinType` is a registered currency.
    fun assert_is_currency<CoinType>() {
        assert(is_currency<CoinType>(), 1);
    }

    /// **************** MODULE SPECIFICATION ****************

    /// # Module Specification

    spec module {
        /// Verify all functions in this module.
        pragma verify = true;
    }

    spec module {
        /// Checks whether currency is registered. Mirrors `Self::is_currency<CoinType>`.
        define spec_is_currency<CoinType>(): bool {
            exists<CurrencyInfo<CoinType>>(CoreAddresses::SPEC_CURRENCY_INFO_ADDRESS())
        }

        /// Returns currency information.
        define spec_currency_info<CoinType>(): CurrencyInfo<CoinType> {
            global<CurrencyInfo<CoinType>>(CoreAddresses::SPEC_CURRENCY_INFO_ADDRESS())
        }
    }
}
}
