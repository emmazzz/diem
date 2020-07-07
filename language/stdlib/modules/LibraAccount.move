address 0x1 {

// The module for the account resource that governs every Libra account
module LibraAccount {
    use 0x1::Libra::{Self, Libra};

    const INVALID_PAYEE_ERROR: u64 = 42;










    // A resource that holds the coins stored in this account
    resource struct LibraAccount<CoinType> {
        balance: Libra<CoinType>,
    }



    /// Withdraw `amount` Libra<CoinType> from the `payer` and
    /// deposits it into the `payee`'s account balance.
    public fun pay_from<CoinType>(
        payer: address,
        payee: address,
        amount: u64,
    ) acquires LibraAccount {

        deposit<CoinType>(
            payee,
            withdraw_from(payer, amount),
        );

    }

    spec fun pay_from {
        requires amount != 0;

        ensures balance_of<CoinType>(payer) ==
            old(balance_of<CoinType>(payer)) - amount;

        ensures balance_of<CoinType>(payee) ==
            old(balance_of<CoinType>(payee)) + amount;

        aborts_if !exists<LibraAccount>(payer);

        aborts_if !exists<LibraAccount>(payee);
    }










    spec module {
        define balance_of<CoinType>(addr: address): u64 {
            global<LibraAccount<CoinType>>(addr).balance.value
        }
    }

    // Withdraw `amount` Libra<CoinType> from the `payer`.
    fun withdraw_from<CoinType>(
        payer: address,
        amount: u64,
    ): Libra<CoinType> acquires LibraAccount {
        let account_balance = borrow_global_mut<LibraAccount<CoinType>>(payer);
        Libra::withdraw(&mut account_balance.balance, amount)
    }

    /// Record a payment of `to_deposit` to `payee`.
    fun deposit<CoinType>(
        payee: address,
        to_deposit: Libra<CoinType>,
    ) acquires LibraAccount {
        // Check that the `to_deposit` coin is non-zero
        let deposit_value = Libra::value(&to_deposit);
        assert(deposit_value > 0, 7);

        // Deposit the `to_deposit` coin
        Libra::deposit(&mut borrow_global_mut<LibraAccount<CoinType>>(payee).balance, to_deposit);
    }

    spec module {
        pragma aborts_if_is_partial = true;
    }
}
}
