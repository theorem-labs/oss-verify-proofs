(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memcpy.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
bytes_at usegs m S src -> length src = Z.to_nat n ->
rw_cells usegs m D [CB (Z.to_nat n) junk] ->
0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
(S + n <= D \/ D + n <= S) ->
mem_inv usegs m ->
evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' D [CB (Z.to_nat n) src])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1c130) fc None m (seg_rom usegs)).
Proof.
intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>61929833015.4964303092338.488548902953.47 00000H00V00dS3LEN2D02D12S02S12N03SEPS3LEN2S02S12N0S3LEN2D02D12N0".
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
[exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
do 15 eexists. split; [reflexivity|]. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ru64s_read : forall m A ws (i : Z) w a,
bytes_at usegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
ov_read_bytes usegs m a 8 = Some (le8 w).
Proof.
intros m A ws i w a Hb Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25273904528.1546081068896.1558870951973.1561555382922.1500000:00D00Q00[S4Hlen3HluS4Hlen3HluS2Hi4Hlen3HluS4Hlen3Hlu".
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read usegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rrw_cells_app_split : forall m A cs1 cs2,
rw_cells usegs m A (cs1 ++ cs2) -> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
destruct H as [[WF B] W].
apply cells_wf_app in WF. destruct WF as [WF1 WF2].
rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
split; [split; [exact WF2 | exact B2] |].
rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.
#[using="Type"] Lemma rrw_cells_app_join : forall m A cs1 cs2,
rw_cells usegs m A cs1 -> rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells usegs m A (cs1 ++ cs2).
Proof.
intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
- apply cells_wf_app. split; assumption.
- rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
- rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). Local Ltac2 Set LiaHints.tbl := fun () => "0050>1311789837.15 19522555985.1824931536571.1553121998162.1863892447207.1800000400:00>00B00HS2H3S2Hi1HS2H0S2HiS2Hi1H".
split; [lia|]. split; [lia|].
intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
+ apply X1. lia.
+ replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15a60) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
/\ stk usegs m' lo (bv_unsigned sp + -64)
/\ rmrep (am_init_st st) m'.
#[using="Type"] Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv usegs m -> rauxv_ok m (bv_unsigned sp) ->
stk usegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
(c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = 0 -> 0 <= c_secret (ctx st) < 2^64 ->
evt usegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x159ac) fc None m (seg_rom usegs)).
Proof.
intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5) & _). unfold rctx_head_cells, rsecw in C1.
unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. atop_facts. unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM. unfold RCTX in MU.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR).
pose proof sec_range as SECR'.
unfold RAUXV_CELL in AVC.
st1. Local Ltac2 Set LiaHints.tbl := fun () => "02=0?11552300008.92 11552300008.93 11552300008.94 11552300008.95 11552300008.96 11555595221.10811801586693.10711805467289.92 11805467289.93 11805467289.94 11805467289.95 11805467289.96 11912744615.93 12280974733.89 12281056739.10412367362435.93 15045097248.87 15224239576.92 15224239576.93 15224239576.94 15224239576.95 15224239576.96 1527479463.92  15330105832.92 15330105832.93 15330105832.94 15330105832.95 15330105832.96 15457446739.92 15457446739.93 15457446739.94 15457446739.95 16496876345.10716576854504.92 16576854504.93 16576854504.94 16576854504.95 16576854504.96 17210337356.87 17351860214.10617646078182.85 17805285100.87 17937675779.11317937675779.11719591727510.10219937319914.10221135219446.10621918414723.93 23811967384.86 24696263440.11324696263440.11725071629079.11325071629079.11725071629079.92 25071629079.93 25071629079.94 25071629079.95 25071629079.96 25314760359.94 26113657110.10727289923224.11327289923224.11727923971379.96 30985415188.87 31787418571.10732799535606.10633039531175.94 34489533625.10735040571675.10335040571675.88 35536403216.11335536403216.11735587154027.11335587154027.11736244065544.88 36671707196.88 36993589379.94 3945979267.94  40356513836.87 40825509068.87 41416020844.87 41809558659.92 42484794827.10743057235856.83 43060403331.95 43928033258.96 46029161400.10646704670696.92 46704670696.93 46704670696.94 46704670696.95 46704670696.96 47439602414.107476165835.107  48484971280.11348484971280.11749705053714.92 49705053714.93 49705053714.94 49705053714.95 49705053714.96 51163085556.11351163085556.11751425718543.11051425718543.96 51481786499.94 51576684520.92 51576684520.93 51576684520.94 51576684520.95 51576684520.96 53427322480.87 53562484459.11353562484459.11753990005404.87 56228262055.93 56537577096.88 58766074614.10659715610898.11360025031335.95 60542728832.88 60561126859.10761252852049.92 61252852049.93 61252852049.94 61252852049.95 61252852049.96 62965819126.10663368099340.87 63370196603.88 6361280528.113 6361280528.117 63967261868.87 64205834651.10764248730225.11765502198668.87 67800801447.94 68314956937.11368314956937.1178374241300.88  9243500491.107 00000=00J00W00d01101401501901=01A01E01I01J01K01L01M01N01V01^01f01n02602702D02Q02^02k03803<03@03D03H03I03V03c04004=04J04K04U04V04W04X04Y04Z04[04e04f04l04m04n04o05005405805<05@05D05E05J05X05f05g06506606@06A06B06K06T06U06V06`06j06n07807907:07;07<07=07>07?07E07F07J07K07X07e08208?08L08M08N08O08P08X08`08h09009809909:09;09<09=09J09W09d0:10:>0:E0:O0:Y0:Z0:[0:`0:j0:k0:l0;00;10;80;?0;F0;M0;T0;^0;_0;`0;a0;b0;c0;g0;h0;i0;j0<70<D0<H0<IS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS1HFS2HBS2HBS2HBS2HBS2HBSSSSSS3BAV2HBS3BAV2HBS3BAV2HBS3BAV2HBS3BAV2HBSS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2HBS2HBS2HBS2HBSS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBSS2AB5ATOPRSSSSSSS2AB5ATOPRSS4INITSSSSS2HBS2HBS2HBS2HBS2HBSS3BAVS2AB3BAV5ATOPRS2AB3BAV5ATOPRSS2AB3SPR5ATOPRSS2AB5ATOPRSFS2LO4LOLES2LO4LOLESSS2AB5ATOPRS2AB5ATOPRS2XRS2AB5ATOPRSSSSSSSS4LOLESS2HBSS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBSSSSS3SPR2HBS3SPR2HBS3SPR2HBS3SPR2HBS3SPR2HBSSSSSS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2AB5ATOPR2HBS2RH2XRS2AB5ATOPRS2AB5ATOPRSSS3SPRS2AB5ATOPRSSS2RHSS2BR2HBS2BR2HBS2BR2HBS2BR2HBS2BR2HBS2AB5ATOPRSSSSSS2BRSSSS2AB2BR5ATOPRS2AB2BR5ATOPRS2BRS".
carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
st1. st1. st1. st1. st1. st1.
st1. rewrite sx32_wz by lia. st1. st1.
st1.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
destruct INIT as [I0|I1].
2:{
rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; atop_facts; lia. }
rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
st1. st1. st1. st1. st1. st1. st1. st1. st1.
Ltac skip_iter i key HB :=
let RD := fresh "RD" in
st1;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ i (wz key) (wa (_ + 8 * i)) HB eq_refl ltac:(lia) eq_refl) as RD end;
st1; try clear RD;
st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
st1.
skip_iter 0 3 AVL.
skip_iter 2 4 AVL. skip_iter 4 5 AVL. skip_iter 6 16 AVL. skip_iter 8 6 AVL.
skip_iter 10 11 AVL. skip_iter 12 12 AVL. skip_iter 14 23 AVL.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ 16 (wz 25) (wa (_ + 8 * 16)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
st1. try clear RD.
st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ 17 (wz rnd) (wa (_ + 8 * 17)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
st1. try clear RD. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
cbn [cells_size csize Nat.add] in FRc;
replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
apply (rw_cells_merge usegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
rewrite app_nil_r in FRm; clear FR
end end.
st1.
call rmemcpy_callZ3.
1:{ exact RND. } 1:{ reflexivity. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
1:{ lazymatch goal with H : mem_inv usegs ?mX |- mem_inv usegs ?mX => exact H end. }
lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz SECRET))] |- _ => rename H into DST end.
st1. st1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (ru64s_read mX _ _ 18 (wz 0) (wa (_ + 8 * 18)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
st1. try clear RD.
st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
lazymatch type of DST with rw_cells _ ?mX _ _ =>
assert (DST8 : rw_cells usegs mX (bv_unsigned sp + -64) [C8 (wz SECRET)])
by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
clear DST end.
st1.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; atop_facts; lia);
pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
clear MUh. unfold RCTX in MUc.
st1. st1.
set (stI := upd_ctx (fun c => set_init_done 1 (set_secret 0 c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
{ eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (pw stI ?q) with (pw st q). unfold wz at 2. rewrite Z.mul_1_r.
lazymatch goal with H : rw_cells usegs ?mX 324152 _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
clear MUc WMc MRX.
st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch goal with Hm : rw_cells usegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells usegs mX (bv_unsigned sp + -56) ?csc |- _ =>
pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
cbn [app] in J2; clear Hm Hc;
lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
apply (rw_cells_merge usegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
end end.
apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
