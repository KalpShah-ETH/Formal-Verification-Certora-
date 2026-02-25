//////////////////////////////////////////////////////////////
//                       METHODS BLOCK                      //
//////////////////////////////////////////////////////////////

methods {

    function totalAssets() external returns (uint256);
    function totalSupply() external returns (uint256);
    function balanceOf(address) external returns (uint256);

    function convertToShares(uint256) external returns (uint256);
    function convertToAssets(uint256) external returns (uint256);

    function previewDeposit(uint256) external returns (uint256);
    function previewWithdraw(uint256) external returns (uint256);
    function previewMint(uint256) external returns (uint256);
    function previewRedeem(uint256) external returns (uint256);

    function deposit(uint256,address) external returns (uint256);
    function withdraw(uint256,address,address) external returns (uint256);
    function mint(uint256,address) external returns (uint256);
    function redeem(uint256,address,address) external returns (uint256);

    function maxWithdraw(address) external returns (uint256);
    function maxDeposit(address) external returns (uint256);
}

//////////////////////////////////////////////////////////////
//                  CONSTRUCTOR BASE CASE                   //
//////////////////////////////////////////////////////////////

// invariant BaseState()
// {
//     preserved constructor() with (env e) {
//         require totalSupply(e) == 0;
//         require totalAssets(e) == 0;
//     }
// }

//////////////////////////////////////////////////////////////
//            CORE ACCOUNTING INVARIANTS                    //
//////////////////////////////////////////////////////////////

invariant AssetsShareConsistency(env e)
    totalSupply(e) == 0
    || convertToAssets(e, totalSupply(e)) == totalAssets(e)
{
}

invariant ZeroSupplyImpliesZeroAssets(env e)
    totalSupply(e) == 0 => totalAssets(e) == 0
{
}

invariant ConvertMonotonic(env e, uint256 a1, uint256 a2)
    a1 <= a2 => convertToShares(e, a1) <= convertToShares(e, a2)
{
}

//////////////////////////////////////////////////////////////
//               ROUNDING SAFETY INVARIANT                  //
//////////////////////////////////////////////////////////////

invariant ShareAssetRoundTrip(env e, uint256 assets)
    totalSupply(e) > 0 && assets <= totalAssets(e)
    => convertToAssets(e, convertToShares(e, assets)) <= assets
{
}

//////////////////////////////////////////////////////////////
//                   PREVIEW CONSISTENCY                    //
//////////////////////////////////////////////////////////////

rule DepositMatchesPreview(env e, address user, uint256 assets)
{
    require assets > 0;
    require user != currentContract;

    uint256 preview = previewDeposit(e, assets);

    uint256 sharesBefore = balanceOf(e, user);
    uint256 supplyBefore = totalSupply(e);

    deposit(e, assets, user);

    assert balanceOf(e, user) == sharesBefore + preview;
    assert totalSupply(e) == supplyBefore + preview;
}

rule WithdrawMatchesPreview(env e, address user, uint256 assets)
{
    require assets > 0;
    require user != currentContract;
    require assets <= maxWithdraw(e, user);

    uint256 preview = previewWithdraw(e, assets);

    uint256 sharesBefore = balanceOf(e, user);

    withdraw(e, assets, user, user);

    assert balanceOf(e, user) == sharesBefore - preview;
}

rule RedeemMatchesPreview(env e, address user, uint256 shares)
{
    require shares > 0;
    require user != currentContract;
    require shares <= balanceOf(e, user);

    uint256 preview = previewRedeem(e, shares);

    uint256 supplyBefore = totalSupply(e);

    redeem(e, shares, user, user);

    assert totalSupply(e) == supplyBefore - shares;
    assert preview <= totalAssets(e);
}

rule NoFreeMint(env e, address user)
{
    uint256 supplyBefore = totalSupply(e);

    mint(e, 0, user);

    assert totalSupply(e) == supplyBefore;
}

invariant MaxDepositNonNegative(env e, address user)
    maxDeposit(e, user) >= 0
{
}

invariant MaxWithdrawBound(env e, address user)
    maxWithdraw(e, user)
    <= convertToAssets(e, balanceOf(e, user))
{
}