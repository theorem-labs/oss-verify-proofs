(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_st RF_huf_rs_pure
  RF_huf_rs_dl RF_huf_rs_cl RF_huf_rs_fin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= wk_acc_hint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac pregs := let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v11 := reg_val 11%Z in let v17 := reg_val 17%Z in let v21 := reg_val 21%Z in
    let v22 := reg_val 22%Z in let v23 := reg_val 23%Z in let v26 := reg_val 26%Z in let v27 := reg_val 27%Z in
    let v28 := reg_val 28%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    let v1 := reg_val 1%Z in let v10 := reg_val 10%Z in let v14 := reg_val 14%Z in let v15 := reg_val 15%Z in
    let v16 := reg_val 16%Z in let v8 := reg_val 8%Z in let v9 := reg_val 9%Z in let v18 := reg_val 18%Z in
    let v19 := reg_val 19%Z in let v20 := reg_val 20%Z in let v24 := reg_val 24%Z in let v25 := reg_val 25%Z in
    idtac "ra=" v1 " t0=" v5 " t1=" v6 " t2=" v7 " s0=" v8 " s1=" v9;
    idtac " a0=" v10 " a1=" v11 " a2=" v12 " a3=" v13 " a4=" v14 " a5=" v15 " a6=" v16 " a7=" v17;
    idtac " s2=" v18 " s3=" v19 " s4=" v20 " s5=" v21 " s6=" v22 " s7=" v23 " s8=" v24 " s9=" v25 " s10=" v26 " s11=" v27;
    idtac " t3=" v28 " t4=" v29 " t5=" v30 " t6=" v31;
    lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mm _) => idtac " pc=" pc " mem=" mm end.

Section CANSEC1. Context {rc : runConstT}.

Section CLA.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x1' x11 x12 x18 x19 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m0 : amem) (RNG : footprint) (HW RK : Z) (ws : list Z).
  Variable Q : machine_state -> Prop.
  Hypothesis HWS : 1 <= zlen ws <= 255.
  Hypothesis HWB : Forall (fun c => 0 <= c < 256) ws.
  Hypothesis HHW : ablk HW (HW + 256).
  Hypothesis HRK : ablk RK (RK + 52).
  Hypothesis RK4 : RK mod 4 = 0.
  Hypothesis DHR : HW + 256 <= RK \/ RK + 52 <= HW.
  Hypothesis ZHW : zshadow m0 HW 256.
  Hypothesis ZRK : zshadow m0 RK 52.
  Hypothesis AWD : appW [(RK, RK + 52)].
  Hypothesis RHW : rng RNG HW 256.
  Hypothesis RHWs : rng RNG (shad HW) (nshad (256 + HW mod 8)).
  Hypothesis RRK : rng RNG RK 52.
  Hypothesis RRKs : rng RNG (shad RK) (nshad (52 + RK mod 8)).

  (* [comment removed for export] *)
  Definition clA_inv (m1 : amem) (rank : list Z) : Prop :=
    u32arr bsegs m1 RK (map (Z_to_bv 64) rank)
    /\ bytes_at bsegs m1 HW (map (Z_to_bv 8) ws)
    /\ munch [(RK, RK + 52)] m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Notation ST pc mm x13 x14 x17 x28 x29 x30 x31 :=
    (MS (mkR x1' sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 12) (Z_to_bv 64 30) (Z_to_bv 64 RK) (Z_to_bv 64 (zlen ws)) (Z_to_bv 64 (-20))
             x11 x12 x13 x14 (Z_to_bv 64 HW) (Z_to_bv 64 (18446744073709551615 - HW)) x17 x18 x19 (Z_to_bv 64 2147450880)
             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma clA_loop : forall f n rank wt m1 (x14 x29 x30 x31 : word),
    Z.of_nat f = zlen ws - n -> 0 <= n < zlen ws ->
    RF_huf_rs_cl.cl_ok n rank wt -> clA_inv m1 rank ->
    (forall m2 rank' wt' (y13 y14 y28 y29 y30 y31 : word),
       collect_loop (skipn (Z.to_nat n) ws) rank wt = Ok (rank', wt') -> RF_huf_rs_cl.cl_ok (zlen ws) rank' wt' -> clA_inv m2 rank' ->
       evtF bsegs RNG Q (ST 0x975f0 m2 y13 y14 (Z_to_bv 64 wt') y28 y29 y30 y31)) ->
    (forall m2 rank' (y13 y14 y17 y28 y29 y30 y31 : word),
       collect_loop (skipn (Z.to_nat n) ws) rank wt = Err ZSTD_error_corruption_detected -> clA_inv m2 rank' ->
       evtF bsegs RNG Q (ST 0x9780c m2 y13 y14 y17 y28 y29 y30 y31)) ->
    evtF bsegs RNG Q (ST 0x97548 m1 (Z_to_bv 64 n) x14 (Z_to_bv 64 wt) (Z_to_bv 64 (n + 1)) x29 x30 x31).
Proof.
intros f. induction f as [|f IH]; intros n rank wt m1 x14 x29 x30 x31 HF HN CO INV KX KE; [lia|].
pose proof INV as INV0.
destruct INV as (RKA & HWA & MU & WM & MI).
pose proof CO as CO0.
destruct CO as (CL & CF & CW).
pose proof (ablk_lin _ _ HHW) as (HWa & HWb & HWc & HWd).
pose proof (ablk_lin _ _ HRK) as (RKa & RKb & RKc & RKd).
unfold AIMG_HI in RKa, HWa.
pose proof (zshadow_appW _ m0 m1 _ _ ZHW MU AWD ltac:(lia) ltac:(lia)) as ZHW1.
pose proof (zshadow_appW _ m0 m1 _ _ ZRK MU AWD ltac:(lia) ltac:(lia)) as ZRK1.
pose proof (byte_Znth ws n HWB HN) as WB.
assert (UB : bv_unsigned (Z_to_bv 8 (Znth n ws)) = Znth n ws)
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; lia).
pose proof (RF_huf_rs_pure.collect_step ws n rank wt HN) as CS.
zstep. wk_go [0x975f0; 0x9780c; 0x97548].
destruct (Z_lt_le_dec 12 (Znth n ws)) as [BIG|SMALL].
{ wk_go [0x975f0; 0x9780c; 0x97548].
  apply (KE m1 rank); [rewrite CS; unfold HUF_TABLELOG_MAX; rewrite (proj2 (Z.ltb_lt 12 (Znth n ws)) BIG); reflexivity | exact INV0]. }
assert (RB : 0 <= Znth (Znth n ws) rank <= n) by (apply (Forall_Znth _ rank (Znth n ws) CF); lia).
wk_go [0x975f0; 0x9780c; 0x97548].
assert (EQA : Z_to_bv 64 (Z.shiftl (Znth n ws) 2 + RK) = wa (RK + 4 * Znth n ws))
  by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia).
set (m2 := write_to_mem m1 (Z_to_bv 64 (Z.shiftl (Znth n ws) 2 + RK)) (le4 (Z_to_bv 64 (Znth (Znth n ws) rank + 1)))) in *.
assert (MU2 : munch [(RK, RK + 52)] m0 m2)
  by (unfold m2; rewrite EQA; apply munch_write_n with (n := 4); [reflexivity|lia|lia|exact MU|cbn; lia]).
assert (WM2 : wmono bsegs m0 m2) by (unfold m2; apply wmono_write; exact WM).
assert (MI2 : mem_inv bsegs m2) by (unfold m2; apply mem_inv_store; [exact MI|exact HS]).
assert (HWA2 : bytes_at bsegs m2 HW (map (Z_to_bv 8) ws))
  by (unfold m2; rewrite EQA; apply bytes_at_write_other_n with (n := 4); [reflexivity|lia|lia|exact HWA|rewrite ?length_map; lia]).
assert (RKA2 : u32arr bsegs m2 RK (upd (map (Z_to_bv 64) rank) (Z.to_nat (Znth n ws)) (Z_to_bv 64 (Znth (Znth n ws) rank + 1))))
  by (unfold m2; rewrite EQA; apply u32arr_write; [exact RKA|rewrite ?length_map; lia]).
pose proof (zshadow_appW _ m0 m2 _ _ ZHW MU2 AWD ltac:(lia) ltac:(lia)) as ZHW2.
pose proof (zshadow_appW _ m0 m2 _ _ ZRK MU2 AWD ltac:(lia) ltac:(lia)) as ZRK2.
clearbody m2. clear MU WM MI HWA RKA HS EQA ZHW1 ZRK1.
wk_go [0x975f0; 0x9780c; 0x97548].
assert (L32 : forall x, Z.land x 4294967295 = x mod 2^32)
  by (intro x; change 4294967295 with (Z.ones 32); apply Z.land_ones; lia).
assert (WTS : forall w0 wt0, 0 <= w0 <= 12 -> 0 <= wt0 <= 2^30 ->
   bv_swrap 32 (Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (bv_swrap 32 (Z.shiftl 1 (w0 mod 32))) 18446744073709551615)) 1)) 18446744073709551615 + wt0)
   = wt0 + 2^w0 / 2).
{ intros w0 wt0 Hw Hwt.
  assert (Hc : bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (bv_swrap 32 (Z.shiftl 1 (w0 mod 32))) 18446744073709551615)) 1) = 2^w0 / 2).
  { assert (w0 = 0 \/ w0 = 1 \/ w0 = 2 \/ w0 = 3 \/ w0 = 4 \/ w0 = 5 \/ w0 = 6 \/ w0 = 7 \/ w0 = 8 \/ w0 = 9 \/ w0 = 10 \/ w0 = 11 \/ w0 = 12) as WC by lia.
    destruct WC as [WC|[WC|[WC|[WC|[WC|[WC|[WC|[WC|[WC|[WC|[WC|[WC|WC]]]]]]]]]]]]; subst w0; vm_compute; reflexivity. }
  assert (Hp : 1 <= 2^w0 <= 4096) by (split; [apply (Z.pow_le_mono_r 2 0 w0); lia | apply (Z.pow_le_mono_r 2 w0 12); lia]).
  rewrite Hc, land64_mod, Z.mod_small by lia.
  unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite Z.mod_small by lia. lia. }
rewrite (L32 (n + 1)), (Z.mod_small (n + 1)) by lia.
rewrite (WTS (Znth n ws) wt) by lia.
assert (HP : 1 <= 2 ^ Znth n ws <= 4096)
  by (split; [apply (Z.pow_le_mono_r 2 0 (Znth n ws)); lia | apply (Z.pow_le_mono_r 2 (Znth n ws) 12); lia]).
assert (CS2 : collect_loop (skipn (Z.to_nat n) ws) rank wt
              = collect_loop (skipn (Z.to_nat (n + 1)) ws) (Zupd (Znth n ws) (Znth (Znth n ws) rank + 1) rank)
                  (wt + 2 ^ Znth n ws / 2)).
{ rewrite CS. unfold HUF_TABLELOG_MAX. rewrite (proj2 (Z.ltb_ge 12 (Znth n ws)) SMALL).
  unfold load, store, shl32. rewrite FseLemmas.Zlength_correct, CL.
  rewrite (proj2 (Z.leb_le 0 (Znth n ws)) ltac:(lia)), (proj2 (Z.ltb_lt (Znth n ws) 13) ltac:(lia)).
  rewrite (proj2 (Z.ltb_lt (Znth n ws) 32) ltac:(lia)). cbn [andb bind].
  unfold u32. rewrite Z.mul_1_l, (Z.mod_small (2 ^ Znth n ws)) by lia.
  rewrite (Z.mod_small (Znth (Znth n ws) rank + 1)) by lia.
  rewrite (Z.mod_small (wt + 2 ^ Znth n ws / 2)) by lia. reflexivity. }
assert (CO2 : RF_huf_rs_cl.cl_ok (n + 1) (Zupd (Znth n ws) (Znth (Znth n ws) rank + 1) rank) (wt + 2 ^ Znth n ws / 2)).
{ split; [unfold Zupd; rewrite upd_nat_length; exact CL|split; [|lia]].
  unfold Zupd. apply RF_huf_rs_cl.Forall_upd_nat; [|lia].
  rewrite Forall_forall in CF |- *. intros v Hv. specialize (CF v Hv). lia. }
assert (RKA3 : u32arr bsegs m2 RK (map (Z_to_bv 64) (Zupd (Znth n ws) (Znth (Znth n ws) rank + 1) rank)))
  by (unfold Zupd; rewrite map_upd_nat; exact RKA2).
assert (INV2 : clA_inv m2 (Zupd (Znth n ws) (Znth (Znth n ws) rank + 1) rank))
  by (split; [exact RKA3|split; [exact HWA2|split; [exact MU2|split; [exact WM2|exact MI2]]]]).
destruct (Z_lt_le_dec (n + 1) (zlen ws)) as [MORE|DONE].
- wk_if_true.
  replace (n + 2) with (n + 1 + 1) by lia.
  apply (IH (n + 1) (Zupd (Znth n ws) (Znth (Znth n ws) rank + 1) rank) (wt + 2 ^ Znth n ws / 2) m2 (Z_to_bv 64 0) _ _ x31);
    [lia | lia | exact CO2 | exact INV2
    | intros m3 rk wt3 y13 y14 y28 y29 y30 y31 E1 E2 E3; apply (KX m3 rk wt3); [rewrite CS2; exact E1|exact E2|exact E3]
    | intros m3 rk y13 y14 y17 y28 y29 y30 y31 E1 E2; apply (KE m3 rk); [rewrite CS2; exact E1|exact E2]].
- wk_go [0x975f0; 0x9780c; 0x97548].
  apply (KX m2 (Zupd (Znth n ws) (Znth (Znth n ws) rank + 1) rank) (wt + 2 ^ Znth n ws / 2));
    [rewrite CS2; replace (Z.to_nat (n + 1)) with (length ws) by lia; apply RF_huf_rs_pure.collect_end
    | replace (zlen ws) with (n + 1) by lia; exact CO2 | exact INV2].
Qed.
End CLA.
End CANSEC1.
