
ghost mathint g_totalethsent{
init_state axiom  g_totalethsent == 0;
}


hook Sstore contributions[KEY address user] uint256 newval (uint256 oldval){
    require(newval < max_uint256); 
    require(oldval < max_uint256);
    
    g_totalethsent = g_totalethsent + newval - oldval;
}



invariant CheckTotalethsentequalstotalcontributions() 
    nativeBalances[currentContract] == g_totalethsent
{
    preserved constructor() with (env e)
{
    require nativeBalances[currentContract] == 0;
}
preserved buyTokens() with (env e){
   
    require e.msg.sender !=currentContract;
}

}   
     