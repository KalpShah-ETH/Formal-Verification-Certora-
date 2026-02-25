methods {
    function totalSupply() external returns (uint256) envfree;
    function balanceOf(address) external returns(uint256) envfree;
}

/*
invariant CheckIntegrity()
    nativeBalances[currentContract] >= totalSupply()
    {
        
        
        //Generic block(global-block)
        preserved with(env e){
            require e.msg.sender !=currentContract;
            require balanceOf(e.msg.sender) <= totalSupply();
        }


    }
*/

rule Checkdepositsequalstoreceived(env e)
{

require e.msg.sender != currentContract;
require balanceOf(e.msg.sender) + e.msg.value <= max_uint256;

mathint ethbalanceBefore=nativeBalances[e.msg.sender];
mathint wethbalanceBefore = balanceOf(e.msg.sender);


deposit(e);

mathint ethbalanceAfter=nativeBalances[e.msg.sender];
mathint wethbalanceAfter = balanceOf(e.msg.sender);

assert ethbalanceAfter == ethbalanceBefore - e.msg.value;
assert wethbalanceAfter == wethbalanceBefore + e.msg.value;

}

rule CheckDepositsNeverReverts(env e){

address holder;

mathint balanceBefore = balanceOf(holder);
require(balanceBefore + e.msg.value <= max_uint256);

mathint totalSupplybefore = totalSupply();
mathint callerbalanceBefore = nativeBalances[e.msg.sender];

deposit@withrevert(e);
bool success = lastReverted;

assert success <=> (totalSupplybefore + e.msg.value > max_uint256) || (callerbalanceBefore < e.msg.value);

}

invariant CheckSolvency()

nativeBalances[currentContract] >= totalSupply()
{
    preserved with (env e){
        require e.msg.sender != currentContract;
   
    }
     preserved withdraw(uint256 amount) with (env e) {
        require balanceOf(e.msg.sender) <= totalSupply();
    }
}