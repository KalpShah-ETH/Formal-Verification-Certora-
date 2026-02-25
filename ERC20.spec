methods{
    function balanceOf(address) external  returns(uint256) envfree;
    function allowance(address, address) external  returns(uint256) envfree;
    function totalSupply() external  returns(uint256) envfree;
}
/*
rule CheckTransfer(env e){
   
    address to;
    uint256 amount;

    require balanceOf(e.msg.sender) + balanceOf(to) <= max_uint256;

    require amount <= balanceOf(e.msg.sender);

    mathint oldBalanceSender = balanceOf(e.msg.sender);
    mathint oldBalanceReceiver = balanceOf(to);

    transfer(e,to,amount);

    mathint senderBalanceAfter = balanceOf(e.msg.sender);
    mathint receiverBalanceAfter = balanceOf(to);


if(to != e.msg.sender)
{
                    assert balanceOf(e.msg.sender) == oldBalanceSender - amount;
                    assert balanceOf(to) == oldBalanceReceiver + amount;
    
}
else
{
    assert senderBalanceAfter == oldBalanceSender;
    assert receiverBalanceAfter == oldBalanceReceiver;

}

}

rule CheckTranferReverts(env e){

    address to;
    uint256 amount;

    mathint senderBalance = balanceOf(e.msg.sender);

    transfer@withrevert(e,to, amount);

    assert lastReverted <=> amount > senderBalance || e.msg.value !=0;

}

rule CheckTransferfrom(env e){

    address holder;
    address to;
    uint256 amount;

    require balanceOf(holder) + balanceOf(to) <= max_uint256;

    mathint oldBalanceSender = balanceOf(holder);
    mathint oldBalanceReceiver = balanceOf(to);

    transferFrom(e,holder,to,amount);

    mathint senderBalanceAfter = balanceOf(holder);
    mathint receiverBalanceAfter = balanceOf(to);

     if (to != holder) {
        assert senderBalanceAfter == oldBalanceSender - amount;
        assert receiverBalanceAfter == oldBalanceReceiver + amount;
    } 
    else {
        assert senderBalanceAfter == oldBalanceSender;
        assert receiverBalanceAfter == oldBalanceReceiver;
    }

}

rule CheckTranferFromReverts(env e){

    address to;
    address holder;
    uint256 amount;

    mathint senderBalance = balanceOf(holder);
    mathint allowance = allowance(holder, e.msg.sender);

    transferFrom@withrevert(e,holder, to, amount);

    assert lastReverted <=> amount > senderBalance || amount > allowance || e.msg.value !=0;

}
*/

//////////////////////////////////////////////////////////////
//                 ALLOWANCE BEHAVIOR RULES                 //
//////////////////////////////////////////////////////////////

rule transferFrom_updatesAllowanceCorrectly(env e) {

    address owner;
    address to;
    uint256 tokens;

    // capture allowance before transfer
    mathint allowanceBefore = allowance(owner, e.msg.sender);

    transferFrom(e, owner, to, tokens);

    mathint allowanceAfter = allowance(owner, e.msg.sender);

    // infinite approval should remain untouched
    if (allowanceBefore == max_uint256) {
        assert allowanceAfter == allowanceBefore;
    } else {
        assert allowanceAfter == allowanceBefore - tokens;
    }
}


rule approve_setsExactAllowance(env e) {

    address spender;
    uint256 value;

    approve@withrevert(e, spender, value);
    bool reverted = lastReverted;

    mathint newAllowance = allowance(e.msg.sender, spender);

    // if call succeeds, allowance must match requested value
    assert !reverted => newAllowance == value;

    // approve should only revert when ETH is accidentally sent
    assert reverted <=> e.msg.value != 0;
}


//////////////////////////////////////////////////////////////
//                 RETURN VALUE GUARANTEES                  //
//////////////////////////////////////////////////////////////

rule transfer_returnsTrueOnSuccess(env e) {

    address to;
    uint256 tokens;

    bool result = transfer@withrevert(e, to, tokens);
    bool reverted = lastReverted;

    // ERC20 spec: successful transfer returns true
    assert !reverted => result == true;
}


rule transferFrom_returnsTrueOnSuccess(env e) {

    address owner;
    address to;
    uint256 tokens;

    bool result = transferFrom@withrevert(e, owner, to, tokens);
    bool reverted = lastReverted;

    assert !reverted => result == true;
}


rule approve_returnsTrueOnSuccess(env e) {

    address spender;
    uint256 value;

    bool result = approve@withrevert(e, spender, value);
    bool reverted = lastReverted;

    assert !reverted => result == true;
}


//////////////////////////////////////////////////////////////
//                     SUPPLY SAFETY                        //
//////////////////////////////////////////////////////////////

rule mint_overflowProtection() {

    address to;
    uint256 tokens;

    mathint supplyBefore = totalSupply();

    mint@withrevert(to, tokens);
    bool reverted = lastReverted;

    // mint must revert on uint overflow
    assert reverted <=> supplyBefore + tokens > max_uint256;
}


rule burn_reducesBalanceAndSupply() {

    address account;
    uint256 tokens;

    // sanity guard (can later be invariant)
    require totalSupply() >= balanceOf(account);

    mathint balanceBefore = balanceOf(account);
    mathint supplyBefore = totalSupply();

    burn(account, tokens);

    mathint balanceAfter = balanceOf(account);
    mathint supplyAfter = totalSupply();

    assert balanceAfter == balanceBefore - tokens;
    assert supplyAfter == supplyBefore - tokens;
}


rule burn_revertsIfInsufficientBalance(env e) {

    address account;
    uint256 tokens;

    mathint balance = balanceOf(account);

    burn@withrevert(account, tokens);
    bool reverted = lastReverted;

    assert reverted <=> balance < tokens;
}

ghost mathint g_sumofuserbalances{
    init_state axiom g_sumofuserbalances == 0;
}

hook Sstore balanceOf [KEY address user] uint256 newval (uint256 oldval) {
    g_sumofuserbalances = g_sumofuserbalances + newval - oldval;

}

hook Sload uint256 balance balanceOf[KEY address user]{
require g_sumofuserbalances >=  balance;
} 

invariant CheckTotalSupply()

 to_mathint(totalSupply()) == g_sumofuserbalances;



