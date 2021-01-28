// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! Tests for multi-agent transactions.

use diem_types::{
    account_config::{self, ReceivedPaymentEvent, SentPaymentEvent},
    on_chain_config::VMPublishingOption,
    transaction::{
        Script, SignedTransaction, TransactionArgument, TransactionOutput, TransactionStatus,
    },
    vm_status::{known_locations, KeptVMStatus},
};
use language_e2e_tests::{
    account::{self, xdx_currency_code, xus_currency_code, Account},
    common_transactions::{multi_agent_mint_txn, multi_agent_swap_txn},
    current_function_name,
    executor::FakeExecutor,
    transaction_status_eq,
};
use transaction_builder::*;

#[test]
fn multi_agent_mint() {
    let mut executor = FakeExecutor::from_genesis_file();
    executor.set_golden_file(current_function_name!());

    let tc = Account::new_blessed_tc();

    // account to represent designated dealer
    let dd = executor.create_raw_account();
    executor.execute_and_apply(
        tc.transaction()
            .script(encode_create_designated_dealer_script(
                account_config::xus_tag(),
                0,
                *dd.address(),
                dd.auth_key_prefix(),
                vec![],
                false, // add_all_currencies
            ))
            .sequence_number(0)
            .sign(),
    );

    // account to represent VASP
    let vasp = executor.create_raw_account();
    executor.execute_and_apply(
        tc.transaction()
            .script(encode_create_parent_vasp_account_script(
                account_config::xus_tag(),
                0,
                *vasp.address(),
                vasp.auth_key_prefix(),
                vec![],
                false, // add_all_currencies
            ))
            .sequence_number(1)
            .sign(),
    );

    let mint_amount = 1_000;
    let tier_index = 0;
    let txn = multi_agent_mint_txn(&tc, &dd, &vasp, 2, mint_amount, tier_index);

    // execute transaction
    let output = executor.execute_transaction(txn);
    assert_eq!(
        output.status(),
        &TransactionStatus::Keep(KeptVMStatus::Executed)
    );

    executor.apply_write_set(output.write_set());

    let updated_tc = executor.read_account_resource(&tc).expect("tc must exist");
    let updated_dd = executor.read_account_resource(&dd).expect("dd must exist");
    let updated_vasp = executor
        .read_account_resource(&vasp)
        .expect("vasp must exist");
    let updated_dd_balance = executor
        .read_balance_resource(&dd, account::xus_currency_code())
        .expect("dd balance must exist");
    let updated_vasp_balance = executor
        .read_balance_resource(&vasp, account::xus_currency_code())
        .expect("vasp balance must exist");
    assert_eq!(0, updated_dd_balance.coin());
    assert_eq!(mint_amount, updated_vasp_balance.coin());
    assert_eq!(3, updated_tc.sequence_number());
    assert_eq!(0, updated_dd.sequence_number());
    assert_eq!(0, updated_vasp.sequence_number());
    assert_eq!(1, updated_dd.sent_events().count());
    assert_eq!(1, updated_vasp.received_events().count());
}
#[test]
fn multi_agent_swap() {
    let mut executor = FakeExecutor::from_genesis_file();
    executor.set_golden_file(current_function_name!());
    // create and publish a sender with 1_000_010 XUS coins
    // and a secondary signer with 100_100 XDX coins.
    let mut sender = executor.create_raw_account_data(1_000_010, 10);
    let mut secondary_signer = executor.create_xdx_raw_account_data(100_100, 100);
    sender.add_balance_currency(xdx_currency_code());
    secondary_signer.add_balance_currency(xus_currency_code());

    executor.add_account_data(&sender);
    executor.add_account_data(&secondary_signer);

    let xus_amount = 10;
    let xdx_amount = 100;

    let txn = multi_agent_swap_txn(
        sender.account(),
        secondary_signer.account(),
        10,
        xus_amount,
        xdx_amount,
    );
    // execute transaction
    let output = executor.execute_transaction(txn);
    assert_eq!(
        output.status(),
        &TransactionStatus::Keep(KeptVMStatus::Executed)
    );

    executor.apply_write_set(output.write_set());

    // check that numbers in stored DB are correct
    let sender_xus_balance = 1_000_010 - xus_amount;
    let secondary_signer_xdx_balance = 100_100 - xdx_amount;
    let updated_sender = executor
        .read_account_resource(sender.account())
        .expect("sender must exist");
    let updated_sender_xus_balance = executor
        .read_balance_resource(sender.account(), account::xus_currency_code())
        .expect("sender xus balance must exist");
    let updated_sender_xdx_balance = executor
        .read_balance_resource(sender.account(), account::xdx_currency_code())
        .expect("sender xdx balance must exist");
    let updated_secondary_signer = executor
        .read_account_resource(secondary_signer.account())
        .expect("secondary signer must exist");
    let updated_secondary_signer_xus_balance = executor
        .read_balance_resource(secondary_signer.account(), account::xus_currency_code())
        .expect("secondary signer xus balance must exist");
    let updated_secondary_signer_xdx_balance = executor
        .read_balance_resource(secondary_signer.account(), account::xdx_currency_code())
        .expect("secondary signer xdx balance must exist");
    assert_eq!(sender_xus_balance, updated_sender_xus_balance.coin());
    assert_eq!(xdx_amount, updated_sender_xdx_balance.coin());
    assert_eq!(xus_amount, updated_secondary_signer_xus_balance.coin());
    assert_eq!(
        secondary_signer_xdx_balance,
        updated_secondary_signer_xdx_balance.coin()
    );
    assert_eq!(11, updated_sender.sequence_number());
    assert_eq!(100, updated_secondary_signer.sequence_number());
    assert_eq!(1, updated_sender.received_events().count(),);
    assert_eq!(1, updated_sender.sent_events().count());
    assert_eq!(1, updated_secondary_signer.received_events().count());
    assert_eq!(1, updated_secondary_signer.sent_events().count());
}
