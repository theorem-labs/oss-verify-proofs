(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tail cut of reac_grant_build_sweep's walk on fuzz_grant's ASan build; it adapts the walk of a function with a side-stack frame of proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v and lib/A/AChd.v, and the caller-journal call of lib/YC20.v:311-365; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) port of lib/A/Prog/GrantBuildSweepTail.v at a working branch eacc832ec38a (blob 24db0f02dea, the blob the walk was ported from), which adapts the walk of a function with a side-stack frame of proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v and lib/A/AChd.v and the caller-journal call of lib/YC20.v:311-365. *)
(* reac_grant_build_sweep (fuzz_grant.asan-ubsan 0x855fc) on image B: the tail's cut lemma (GrantBuildSweepLib.v,
   bs_tail_spec). From the instruction after the width loop (0x85890), with the 3 * width values in the frame's
   values buffer, through al's shadow check re-read through the slot at s1 + 48 (on z = false the slow path
   0x85a60 comes back to 0x8589c; the report call at 0x85a6c is not reached), the call of
   reac_ctrl_build_grant_sweep (s, mx, base, width, F + 32) at 0x858b0, the 15 shadow bytes of the values buffer
   back to 0xf8, the retired magic at F, the 32 shadow bytes of the frame to 0xf5, the inlined flag store at
   0x85994 (through the pointer at F + 248) that releases the side-stack frame, the epilogue and the return.
   Image B differs from image A here in: the arguments come from the realigned frame's slots (s1 + 8, 16, 56) and
   from al (base, `lbu a2,0(s6)`); the callee's contract (GrantBContracts.v) has the premise base + w < 2 ^ 31,
   states the row buffer apart from image B by IMG_LO_B / IMG_TOP_B, and keeps its journal at k (its tcj_kept
   guards the set of written bytes with bgs_ok, as image A's does; TBGS_KEEP below is derived from that); and the
   read-only data reach the call through image B's own bytes (rod_img_kept), not through arodata_ok_journalP. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantSyms GrantList GrantAddr GrantTop GrantPa GrantPaLib GrantFrame GrantRo YC1g YC1h YC1i YC45 YC85
ACj1 ACbf GrantACjr GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBuildSweepLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* What the call of reac_ctrl_build_grant_sweep keeps of the regions the walk goes on with: the saved registers
   and the realigned frame (above its stack), the own frame's header and tail, and the frame's shadow (not the
   rows it writes, HEF); the frame bytes are there after it (HFp). *)
Local Ltac bt_kept HK HJx AG HEF HFp Hfin F fpos :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _);
[exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; zconst_lits; lia | unfold ESTACK, ASTACK; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _);
[exact HK | exact HJx | evalE AG | unfold ESTACK, ASTACK; zconst_lits; lia | unfold ESTACK, ASTACK; zconst_lits; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _);
[ exact HK | evalE AG | exact Hfin
| left; fold F; change (fs_frame_bytes 2) with 256; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn beta; apply HEF; unfold SB; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (proj1 (HFp a ltac:(lia))) ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _);
[ exact HK | evalE AG | exact Hfin
| right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn beta; apply HEF; unfold SB; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; lia ]
| |- ?g => idtac "KEPT-NORULE" g; fail
end.
(* Unpack a cut's facts (bs_ctx, bs_env, bs_mem) into the names the walk uses: the entry facts (HPRE ..), the
   atoms' values (EE, E32 .. E621, E10 .. E13), the journal HJ2, the stack above sp HUP, the read-only data HROD3,
   the values HVALS, the table HOBJ, the own frame F (flag FL) and its bounds, al's frame (cid, pos) and its
   bounds, and the image facts. Image A's lib/A/Prog/GrantBuildSweepLib.v bs_cut_intro, over image B's cut. *)
Local Ltac bt_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec :=
let L := rnLAWS in
destruct HCTX as (HPRE & Hroom & Htop32 & HROD & H10 & H11 & H12 & H13 & Rs & Rmx & Htx & HTlen & H01 & HTL & HSB &
Hsn & Haln & Hw1 & Hb8 & Hbw & Hfin & Hcid0 & Hflo & Hfhi & Hal8 & Hfrs2 & Eab & (fS2 & ES2) & Hsp1 & Hsp1al);
destruct HENV as (HEI & EE & E32 & E33 & E34 & E35 & E36 & E60 & RF & E528 & E529 & E619 & E620 & E621);
destruct HMEM as (HJ2 & HUP & HROD3 & HVALS & HOBJ);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
assert (FFS : BSW_STK = 4832) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
lazymatch type of H10 with getr _ _ = w64 ?v => assert (E10 : ew Ec 10 = Z_to_bv 64 v) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10) end;
lazymatch type of H11 with getr _ _ = w64 ?v => assert (E11 : ew Ec 11 = Z_to_bv 64 v) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11) end;
lazymatch type of H12 with getr _ _ = w64 ?v => assert (E12 : ew Ec 12 = Z_to_bv 64 v) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12) end;
lazymatch type of H13 with getr _ _ = w64 ?v => assert (E13 : ew Ec 13 = Z_to_bv 64 v) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13) end;
lazymatch type of H10 with getr ?rg _ = _ => assert (Usp : bv_unsigned (ew Ec 2) = spZ rg) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity) end;
assert (AG : forall n, (n < 33)%nat -> ew Ec n = ew Ec n) by (intros; reflexivity);
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by (intros; reflexivity);
img_factsF Ec; img_hull_factsF;
pose proof (proj1 HJ2) as HAR2;
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity);
destruct (al_frames _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres);
destruct (frames_bounds _ _ L _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img;
pose proof (frm_off_imgB _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFIMG;
rewrite IMG_LO_B_val, IMG_TOP_B_val in HFIMG;
destruct (frames_bounds _ _ L ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
destruct (frame_al64 _ _ ly S W mem md cid pos HAR Hfin) as (Hf64 & Hfb64 & Hfb64');
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin);
let fl1 := fresh "fl1" in let fl2 := fresh "fl2" in let Efl := fresh "Efl" in
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl);
pose proof (sep_frames_pos _ _ L ly S2 _ _ _ (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC;
unfold zdisjoint, frame_rng in HdFC; cbn [fst snd] in HdFC;
destruct (al_blocks _ _ L ly S W mem md _ _ HAR Htx) as (_ & Htx4096 & Htxceil & Htxia & _);
change (req_size ATx.TX_SIZE) with 460 in Htxceil, Htxia;
pose proof Htx as HtxS2; rewrite <- Eab in HtxS2;
pose proof (sep_block_frame _ _ L ly S2 W _ _ _ _ 2 fpos HAR2 HtxS2 Hfin2) as HtxF;
unfold zdisjoint in HtxF; cbn [fst snd] in HtxF; change (req_size ATx.TX_SIZE) with 460 in HtxF;
change (fs_frame_bytes 2) with 256 in *;
let F := fresh "F" in let FL := fresh "FL" in
set (F := frame_addr ly 2 fpos) in *; set (FL := flag_addr ly 2 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : F / 8 + 32 <= 17592184995840) by (rewrite <- (Z.div_add F 32 8) by lia; apply Z.div_le_upper_bound; lia);
lazymatch type of H12 with getr _ _ = w64 ?al =>
assert (Hal512 : 512 <= al / 8 < 17592186044416) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia);
assert (Hal8d : al = 8 * (al / 8)) by (pose proof (Z.div_mod al 8 ltac:(lia)); lia) end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* ---- helpers --------------------------------------------------------------- *)
(* A byte chunk of a region of the symbolic state is the byte in memory. *)
Lemma bt_chunk_aview : forall E ss (H : word -> bool) msX i n b lo hi wlo whi cs od e v,
st_ok SEGS E ss (restrict H msX) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
aview SEGS H (ms_mem msX) (b + od) = Some v.
Proof.
intros E ss H msX i n b lo hi wlo whi cs od e v HS Hi Hb Hc He Hv.
pose proof (st_ok_region_nth E ss (restrict H msX) i _ HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (field_of_region E _ n b cs lo hi wlo whi od 1%N e v HR Hb Hc He ltac:(cbn; lia) ltac:(cbn; lia)) as V.
exact (aview_of_val_mem1 SEGS H (ms_mem msX) (b + od) v V Hv).
Qed.
(* Shadow bytes 0 over whole granules mark the bytes usable. *)
Lemma bt_ra_zero : forall (rd : Z -> option Z) F k n, F mod 8 = 0 -> 0 <= k -> 0 <= n ->
(forall i, 0 <= i < n -> rd (SB + F / 8 + k + i) = Some 0) -> range_addressable rd SHADOW_OFF (F + 8 * k) (8 * n).
Proof.
intros rd F k n HF Hk Hn Hz. apply zero_shadow_range.
- rewrite Z.add_mod, HF by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- rewrite Z.mul_comm. apply Z_mod_mult.
- intros i Hi. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
replace ((F + 8 * k) / 8) with (F / 8 + k).
+ replace (8 * n / 8) with n in Hi by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
replace (SB + (F / 8 + k) + i) with (SB + F / 8 + k + i) by lia. apply Hz. lia.
+ rewrite Z.mul_comm, Z.div_add by lia. reflexivity.
Qed.
(* Alignment facts lia cannot see (div and mod are atoms to it here). *)
Lemma bt_mod8 : forall F k, F = 32 * (F / 32) -> (F + 8 * k) mod 8 = 0.
Proof. intros F k H. rewrite H. replace (32 * (F / 32) + 8 * k) with ((4 * (F / 32) + k) * 8) by lia. apply Z_mod_mult. Qed.
Lemma bt_mod8' : forall F, F = 32 * (F / 32) -> F mod 8 = 0.
Proof. intros F H. rewrite <- (Z.add_0_r F) at 1. replace 0 with (8 * 0) by reflexivity. exact (bt_mod8 F 0 H). Qed.
Lemma bt_mod16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q Hq]. exists (2 * q). lia.
Qed.
(* The rows' length: 34 bytes for each of the 8 + 3w rows. *)
Lemma bt_len_chan : forall base vals c, length (ga_chan base vals c) = 102%nat.
Proof. intros. unfold ga_chan, ga_row. rewrite !length_app, !length_GA. reflexivity. Qed.
Lemma bt_len_chans : forall base vals l, length (concat (map (ga_chan base vals) l)) = (102 * length l)%nat.
Proof. intros base vals l. induction l as [|c l IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, IH, bt_len_chan. lia. Qed.
Lemma bt_len_SWEEP : forall base w vals, (1 <= w)%nat -> length (SWEEP base w vals) = (34 * (8 + 3 * w))%nat.
Proof.
intros base w vals Hw. unfold SWEEP. rewrite !length_app, bt_len_chan, bt_len_chans, length_seq, GBall_split, !length_app, !length_GB.
unfold HEAD_ACK34, HEAD_MARK34. rewrite !length_bl. cbn [length HEAD_ACK34z HEAD_MARK34z]. lia.
Qed.
(* The call lays the rows down exactly when bsw_ok holds (al <> 0 and the width checks passed before the loop). *)
Lemma bt_bgs_bsw : forall s V al mx base w, al <> 0 -> 1 <= w <= 40 -> 0 <= base -> base + w <= 48 ->
C.bgs_ok s V mx base w -> bsw_ok s al mx base w = true.
Proof.
intros s V al mx base w Hal Hw Hb Hbw (Hs & HV & _ & _ & Hm). rewrite bsw_ok_go by assumption.
apply Z.leb_le. unfold C.bgs_rows in Hm. lia.
Qed.
Lemma bt_bsw_bgs : forall s V al mx base w, V <> 0 -> bsw_ok s al mx base w = true -> C.bgs_ok s V mx base w.
Proof.
intros s V al mx base w HV Hb. destruct (bsw_ok_spec s al mx base w Hb) as (Hs & Hal & Hw & Hb0 & Hbw & Hm).
unfold C.bgs_ok, C.bgs_rows. repeat split; lia.
Qed.
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* the program function it calls, as GrantBContracts.v states it *)
Hypothesis TBGS : C.tb_reac_ctrl_build_grant_sweep_spec B.
(* ---- the callee's contract with its post as a parameter ------------------ *)
(* C.tb_reac_ctrl_build_grant_sweep_spec B, word for word, with the post-condition abstracted. *)
Definition tbgs_spec_with
(P : Z -> Z -> list (Z * Z) -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> list (Z * Z) ->
alayout -> astate -> world SEGS -> (word -> option byte) -> Z -> bvmap 5 word -> Z -> Z -> Z -> Z -> Z -> list byte ->
world SEGS -> config -> Prop) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s mx base w V : Z)
(vals : list byte) (cl : list (Z * Z * Z)),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 s -> getr regs 11 = w64 mx -> getr regs 12 = w64 base ->
getr regs 13 = w64 w -> getr regs 14 = w64 V ->
0 <= s < 2 ^ 63 -> - 2 ^ 31 <= mx < 2 ^ 31 -> 0 <= base < 256 -> - 2 ^ 31 <= w < 2 ^ 31 -> 0 <= V < 2 ^ 63 ->
base + w < 2 ^ 31 ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) cl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - C.STK_reac_ctrl_build_grant_sweep -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 8 ->
(1 <= w -> V <> 0 ->
length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals /\
garr8 SEGS (mrestrict (w_H W) memc) V (map bv_unsigned vals) /\
C.tsrc_ok W memc (spZ regs) V (3 * w) /\
afobj SEGS B lyc Sc W memc V (3 * w) /\
(spZ regs <= V \/ V + 3 * w <= spZ regs - C.STK_reac_ctrl_build_grant_sweep)) ->
(C.bgs_ok s V mx base w ->
amem_range s (34 * C.bgs_rows w) /\ s + 34 * C.bgs_rows w <= 2 ^ 47 - 8 /\
(s + 34 * C.bgs_rows w <= IMG_LO_B \/ IMG_TOP_B <= s) /\
C.twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) s (34 * C.bgs_rows w) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s (34 * C.bgs_rows w) /\
shadow_hull_vis (aview SEGS (w_H W) memc) s (34 * C.bgs_rows w) /\
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 34 * C.bgs_rows w <= b + req_size m) /\
(spZ regs <= s \/ s + 34 * C.bgs_rows w <= spZ regs - C.STK_reac_ctrl_build_grant_sweep) /\
(V + 3 * w <= s \/ s + 34 * C.bgs_rows w <= V)) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_build_grant_sweep) regs memc mdc)
(P STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
Lemma tbgs_spec_with_C : C.tb_reac_ctrl_build_grant_sweep_spec B -> tbgs_spec_with (C.tb_reac_ctrl_build_grant_sweep_post B).
Proof. exact (fun H => H). Qed.
(* The callee's post as image A states it (lib/A/Prog/CtrlBuildGrantSweepSpec.v tbgs_post, a working branch
   eacc832ec38a), with tcj_kept's set of bytes the call may write guarded by bgs_ok: GrantBContracts.v's post states
   the same text (C.tb_reac_ctrl_build_grant_sweep_post). *)
Definition tbgs_post_g (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (s mx base w V : Z) (vals : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
(exists f, S2 = set_fs f Sc) /\
getr regs2 10 = w64 res /\
C.tcj_kept B C.STK_reac_ctrl_build_grant_sweep lyc Sc W memc W2 mem2 (spZ regs)
(fun a => C.bgs_ok s V mx base w /\ s <= a < s + 34 * C.bgs_rows w) /\
(C.bgs_ok s V mx base w /\ res = C.bgs_rows w /\
garr8 SEGS (mrestrict (w_H W2) mem2) s (map bv_unsigned (SWEEP base (Z.to_nat w) vals))
\/ ~ C.bgs_ok s V mx base w /\ res = -1 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - C.STK_reac_ctrl_build_grant_sweep <= a < spZ regs) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i))).
(* GrantBContracts.v's post, and on the -1 path (not bgs_ok) the caller's frames and their shadow unchanged:
   the one clause the -1 exit needs (the flag pointer at F + 248 and F's shadow), which tcj_kept's bgs_ok guard
   gives (tbgs_keep_of_g). *)
Definition tbgs_post_keep (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (s mx base w V : Z) (vals : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => C.tb_reac_ctrl_build_grant_sweep_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals W2 c2 /\
(~ C.bgs_ok s V mx base w ->
exists regs2 mem2 md2, c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
(* Image A's form of the contract gives this one. *)
Lemma tbgs_keep_of_g : tbgs_spec_with tbgs_post_g -> tbgs_spec_with tbgs_post_keep.
Proof.
unfold tbgs_spec_with. intros HG STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s mx base w V vals cl. intros.
eapply SRr_mono; [eapply HG; eassumption|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & Ec & HJ & HP & Hfr & Hab & Hfs & Ha0 & (K1 & K2 & K3 & K4 & K5 & K6) & Hres).
split.
- (* GrantBContracts.v's post is image A's form word for word (its tcj_kept is guarded by bgs_ok), so each
     clause is the hypothesis's own. *)
exists ly2, S2, regs2, mem2, md2, res. split; [exact Ec|]. split; [exact HJ|]. split; [exact HP|]. split; [exact Hfr|].
split; [exact Hab|]. split; [exact Hfs|]. split; [exact Ha0|]. split; [|exact Hres].
exact (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 K6))))).
- intros Hnb. exists regs2, mem2, md2. split; [exact Ec|].
intros cid pos a Hin Ha. apply (K4 cid pos a Hin Ha). intros [Hb _]. exact (Hnb Hb).
Qed.
(* GrantBContracts.v states tcj_kept with the bytes s .. s + 34 bgs_rows w guarded by bgs_ok (image A's form: the
   -1 path writes no byte of its caller's). On the -1 path, bsw_ok false, nothing bounds s, so only the guard
   keeps the flag pointer at F + 248 the exit reads. This hypothesis is used on that path only; the closing
   theorem (GrantBuildSweepWalk.v) gives it as tbgs_keep_of_g of the contract, through tbgs_spec_with_C. *)
Hypothesis TBGS_KEEP : tbgs_spec_with tbgs_post_keep.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* The rows the call may write lie below the allocator's ceiling. *)
Lemma bt_E_low : forall ly S W mem md s V al mx base w a,
AR SEGS B ly S W mem md -> al <> 0 -> 1 <= w <= 40 -> 0 <= base -> base + w <= 48 ->
(bsw_ok s al mx base w = true -> exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) ->
alloc_ceiling <= a -> ~ (C.bgs_ok s V mx base w /\ s <= a < s + 34 * C.bgs_rows w).
Proof.
intros ly S W mem md s V al mx base w a HAR Hal Hw Hb Hbw HSB Ha [Hbg Has].
destruct (HSB (bt_bgs_bsw s V al mx base w Hal Hw Hb Hbw Hbg)) as (sb & sn & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS ly S W mem md sb sn HAR Hin) as (_ & H4096 & Hceil & _).
assert (Hrq : req_size sn = sn) by (unfold req_size; destruct (Z.eqb_spec sn 0); lia).
unfold C.bgs_rows in Has. lia.
Qed.
Lemma pb_bs_tail : bs_tail_spec B.
Proof.
unfold bs_tail_spec.
intros z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos Ec ms3 md3 HCTX HENV HS HMEM.
bt_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec.
assert (FBG : C.STK_reac_ctrl_build_grant_sweep = 4624) by reflexivity.
(* the values buffer and image B's bytes stay as they are up to the call *)
assert (HKV : forall a, F + 32 <= a < F + 32 + 3 * w -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (HIMG : forall a, 0x10000 <= a < 0x5fb000 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
(* ---- al's shadow check (decided by the cell's facts) and the arguments; to the call of
   reac_ctrl_build_grant_sweep (0x858b0) ---- *)
destruct z.
all: paj_run_shc RUNP RUNC HS HJ2; [awrFL AG fpos F EFA0 |].
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hw1 HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c
Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: upd_rngW HIMG HFr ltac:(clear - Ha_rng; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 HFIMG HF4096 HFceil HF8lo HF8hi HF8c
Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
(* the disjunctive placement facts the rest does not use (they make every lia below case-split) *)
all: clear HtxF HdFC HFIMG HFhigh_img Hfhigh_img.
all: prreg HS (10%bv : bv 5) Ra0.
all: prreg HS (11%bv : bv 5) Ra1.
all: prreg HS (12%bv : bv 5) Ra2.
all: prreg HS (13%bv : bv 5) Ra3.
all: prreg HS (14%bv : bv 5) Ra4.
all: prreg HS (1%bv : bv 5) Rra.
all: prreg HS (2%bv : bv 5) Rsp.
all: prreg HS (3%bv : bv 5) Rgp.
all: prreg HS (4%bv : bv 5) Rtp.
all: prreg HS (8%bv : bv 5) Rs0.
(* the values buffer's shadow (bytes 4..18 of F's) is marked usable *)
all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (ZV : forall j, 4 <= j < 19 -> aview SEGS (w_H W) (ms_mem msX) (SB + F / 8 + j) = Some 0)
by (intros j Hj;
assert (Hjs : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18) by lia;
repeat (destruct Hjs as [-> | Hjs]); try subst j;
(eapply (bt_chunk_aview Ex ssx (w_H W) msX 2%nat); [exact HS | reflexivity | rewrite E529; apply unsigned_lit_small; unfold SB; lia | cbn; tauto | reflexivity | lia])) end.
(* the saved ra and s0, for the call chain *)
all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 6 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; try rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; try rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0
end; clear HRstk end.
(* the read-only data: image B's bytes are as they were at the cut *)
all: pose proof (rod_img_kept B W W _ _ HIMG HROD3) as HROD5.
all: assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
all: assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
all: assert (Hal8sp : spZ regs mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (2 * q); lia).
all: assert (Hch1 : achain ly (aview SEGS (w_H W) (ms_mem ms)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch))
by (replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(lia) Hal8sp ltac:(lia) ltac:(lia))).
all: assert (SP3 : spZ (ms_regs ms) = sp1) by (unfold spZ at 1; rewrite Rsp; evalE AG).
all: assert (S03 : s0Z (ms_regs ms) = spZ regs) by (unfold s0Z; rewrite Rs0; evalE AG).
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpc & _).
all: change (fs_frame_bytes 2) with 256 in HFpc.
all: fold F in HFpc.
all: assert (HRAV : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (F + 32) (3 * w))
by (apply (range_addressable_sub _ _ (F + 8 * 4) (8 * 15)); [| lia | lia];
apply bt_ra_zero; [exact (bt_mod8' F HFq) | lia | lia |]; intros i Hi;
replace (SB + F / 8 + 4 + i) with (SB + F / 8 + (4 + i)) by lia; apply ZV; lia).
(* bsw_ok decides which form of the callee's contract the walk takes: GrantBContracts.v's when the rows are laid
   down, TBGS_KEEP on the -1 path *)
all: assert (Hbsw : bsw_ok s al mx base w = true \/ bsw_ok s al mx base w = false)
by (destruct (bsw_ok s al mx base w); [left | right]; reflexivity).
all: destruct Hbsw as [Hbsw | Hbsw].
all: pmkst HS.
all: rewrite pa_sigma_reac_ctrl_build_grant_sweep.
all: fs_roF HS.
all: eapply SRr_bind.
1, 3, 5, 7: (lazymatch goal with
| Hb : bsw_ok _ _ _ _ _ = ?bv |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
change (mkCfg (mkst (ms_regs msX) (Z_to_bv 64 (BASE + AF_reac_ctrl_build_grant_sweep)) (ms_mem msX) (seg_rom SEGS)) mdX)
with (cfg_at SEGS (BASE + AF_reac_ctrl_build_grant_sweep) (ms_regs msX) (ms_mem msX) mdX);
let TB := lazymatch bv with true => constr:(tbgs_spec_with_C TBGS) | false => constr:(TBGS_KEEP) end in
eapply (TB BSW_STK (spZ regs) (C.tb_reac_grant_build_sweep_FP s al mx base w) ly S W mem md [(2, fpos)] ly S2 W (ms_mem msX) mdX 0 (ms_regs msX)
s mx base w (F + 32) (sweep_vals T tx base (Z.to_nat w)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ2 HROD5) end;
[ (* ra *) rewrite Rra; apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]
| unfold raZ; rewrite Rra; pose proof pa_B_ok as HB; rewrite unsigned_lit_small by lia; lia
| rewrite Rgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| (* a0 = s *) rewrite Ra0; unfold w64; evalE AG
| (* a1 = mx *) rewrite Ra1; unfold w64; evalE AG
| (* a2 = base *) rewrite Ra2; unfold w64; evalE AG
| (* a3 = w *) rewrite Ra3; unfold w64; evalE AG
| (* a4 = F + 32 *) rewrite Ra4; unfold w64; evalE AG
| lia | lia | lia | lia | lia | lia
| rewrite SP3, S03; exact Hch1
| rewrite SP3; exact (bt_mod16 sp1 Hsp1al)
| rewrite SP3, FBG, FFS; lia
| rewrite SP3; lia
| rewrite Hfrs2; cbn [length]; lia
| (* the values the caller hands in *)
intros _ _; rewrite SP3;
assert (Hlen : length (sweep_vals T tx base (Z.to_nat w)) = Z.to_nat (3 * w)) by (rewrite length_sweep_vals; lia);
split; [exact Hlen|];
split; [apply sweep_vals_legal; [exact H01 | exact HTL | lia | rewrite Z2Nat.id by lia; lia]|];
split; [rewrite firstn_all2 in HVALS by (rewrite length_sweep_vals; lia);
refine (garr8_aview_kept SEGS _ _ _ _ _ _ _ HVALS); intros a Ha; apply HKV; rewrite length_map, Hlen in Ha; lia|];
split; [unfold C.tsrc_ok; split;
[ intros a Ha; split; [apply aview_some_of_apresent; exact (proj1 (HFpc a ltac:(lia))) | rewrite Hes; lia] |];
split; [exact HRAV|];
split; [exact (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W _ _ 2 fpos (F + 32) (3 * w) (proj1 HJ2) Hfin2
ltac:(fold F; lia) ltac:(change (fs_frame_bytes 2) with 256; fold F; lia) ltac:(lia))|];
split; [exact (amem_range_sub_app F 256 (F + 32) (3 * w) HFhigh HFceil ltac:(lia) ltac:(lia) ltac:(lia)) | lia] |];
split; [unfold afobj; split; [exists 2, fpos; split; [exact Hfin2|]; fold F; change (fs_frame_bytes 2) with 256;
split; [lia|]; split; [exact (bt_mod8' F HFq)|]; lia|];
split; [replace (F + 32) with (F + 8 * 4) by lia; exact (bt_mod8 F 4 HFq) | exact HRAV]|];
right; rewrite FBG; lia
| (* the row buffer, a heap block's part *)
intros Hbg; rewrite SP3;
let Hbsw' := fresh "Hbsw'" in
pose proof (bt_bgs_bsw s (F + 32) al mx base w Haln Hw1 ltac:(lia) Hbw Hbg) as Hbsw';
destruct (HSB Hbsw') as (sb & sn & Hsbin & Hsblo & Hsbhi);
assert (Hsbin2 : In (sb, sn) (ablocks B ly S2)) by (rewrite Eab; exact Hsbin);
destruct (al_blocks _ _ LAWS _ _ _ _ _ sb sn (proj1 HJ2) Hsbin2) as (_ & Hsb4096 & Hsbceil & Hsbapp & Hsbpres & _);
assert (Hrq : req_size sn = sn) by (unfold req_size; destruct (Z.eqb_spec sn 0); lia);
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ sb sn 2 fpos (proj1 HJ2) Hsbin2 Hfin2) as HdBF;
unfold zdisjoint in HdBF; cbn [fst snd] in HdBF; change (fs_frame_bytes 2) with 256 in HdBF; fold F in HdBF;
pose proof (blk_off_imgB B ly S2 W _ _ sb sn (proj1 HJ2) Hsbin2) as HsbIMG;
rewrite Hrq in Hsbceil, Hsbapp, Hsbpres, HdBF, HsbIMG;
unfold C.bgs_rows;
split; [apply (amem_range_of_block SEGS B LAWS ly S2 _ _ _ sb sn _ _ (proj1 HJ2) Hsbin2); rewrite ?Hrq; lia|];
split; [lia|];
split; [destruct HsbIMG as [HsbIMG | HsbIMG]; [left | right]; lia|];
split; [unfold C.twr_ok; intros a Ha;
split; [right; left; split; [unfold C.tb_reac_grant_build_sweep_FP; rewrite Hbsw'; apply inFP_cons; left; lia | exists sb, sn; split; [exact Hsbin2 | rewrite Hrq; lia]] |];
split; [exact (proj1 (Hsbpres a ltac:(lia)))|];
split; [exact (proj2 (Hsbpres a ltac:(lia))) | rewrite Hes; lia] |];
split; [apply (range_addressable_of_block SEGS B LAWS ly S2 _ _ _ sb sn _ _ (proj1 HJ2) Hsbin2); rewrite ?Hrq; lia|];
split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly S2 _ _ _ sb sn _ _ (proj1 HJ2) Hsbin2); rewrite ?Hrq; lia|];
split; [exists sb, sn; split; [exact Hsbin2 | rewrite Hrq; lia]|];
split; [right; rewrite FBG; lia | lia] ]).
(* ---- after the call: what it leaves ---- *)
all: cbv beta; intros W6 c6 _ Hpost6.
all: lazymatch goal with Hb : bsw_ok _ _ _ _ _ = false |- _ => destruct Hpost6 as [Hpost6 Hxk] | _ => idtac end.
all: destruct Hpost6 as (ly6 & S6 & regs6 & mem6 & md6 & res & -> & HJ6 & HP6 & Hfrs6 & Hab6 & (fS6 & ES6) & Ha06 & HK6 & Hres).
all: rewrite SP3 in HK6, Hres.
all: destruct HK6 as (K1 & K2 & K3 & K4 & K5 & K6).
(* What the call keeps, in image A's form: above the allocator's ceiling nothing but its own stack, and of the
   heap blocks and the frames nothing but the rows when it lays them down. With the rows laid down they lie in a
   heap block below the ceiling (bt_E_low); on the -1 path the post's own clauses and TBGS_KEEP give it. *)
all: lazymatch goal with
| Hb : bsw_ok _ _ _ _ _ = true |- _ =>
pose proof (bt_bsw_bgs s (F + 32) al mx base w ltac:(lia) Hb) as Hbg;
destruct Hres as [(_ & Hresv & Hrows) | (Hn & _)]; [| exfalso; exact (Hn Hbg)];
assert (HKc : acall_kept SEGS B ly S2 W (ms_mem ms) W6 mem6 (sp1 - C.STK_reac_ctrl_build_grant_sweep) sp1
(fun a => C.bgs_ok s (F + 32) mx base w /\ s <= a < s + 34 * C.bgs_rows w))
by (split; [intros a Ha Hns; apply (K1 a Ha Hns); intros Hr;
exact (bt_E_low ly S W mem md s (F + 32) al mx base w a HAR Haln Hw1 ltac:(lia) Hbw HSB ltac:(lia) Hr)|];
split; [intros b m i Hbm Hi Hn; apply (K2 b m i Hbm Hi); intros Hr; exact (Hn Hr)|];
split; [exact K3|];
split; [intros cid0 pos0 a Hin Hr Hn; apply (K4 cid0 pos0 a Hin Hr); intros Hr'; exact (Hn Hr')|];
exact (conj K5 K6))
| Hb : bsw_ok _ _ _ _ _ = false |- _ =>
assert (Hnbg : ~ C.bgs_ok s (F + 32) mx base w)
by (intros Hbg; rewrite (bt_bgs_bsw s (F + 32) al mx base w Haln Hw1 ltac:(lia) Hbw Hbg) in Hb; discriminate Hb);
destruct Hres as [(Hbg & _) | (_ & Hresv & HKhi & HKbl)]; [exfalso; exact (Hnbg Hbg) |];
destruct (Hxk Hnbg) as (regs2 & mem2 & md2 & Ec6 & HFK);
injection Ec6; intros; subst regs2 mem2 md2;
assert (HKc : acall_kept SEGS B ly S2 W (ms_mem ms) W6 mem6 (sp1 - C.STK_reac_ctrl_build_grant_sweep) sp1
(fun a => C.bgs_ok s (F + 32) mx base w /\ s <= a < s + 34 * C.bgs_rows w))
by (split; [intros a Ha Hns; exact (HKhi a Ha Hns)|];
split; [intros b m i Hbm Hi _; exact (HKbl b m i Hbm Hi)|];
split; [exact K3|];
split; [intros cid0 pos0 a Hin Hr _; exact (HFK cid0 pos0 a Hin Hr)|];
exact (conj K5 K6));
clear Hxk HKhi HKbl HFK
end.
all: clear K1 K2 K3 K4 K5 K6.
all: assert (Hfin6 : In (2, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin2).
all: pose proof HJ6 as (_ & Hly6 & _).
all: destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR Hly6) as (_ & EFA6 & _).
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin6) as (_ & _ & HFp6 & HFSp6).
all: rewrite EFA6 in HFp6, HFSp6.
all: change (fs_frame_bytes 2 / 8) with 32 in HFSp6.
all: change (fs_frame_bytes 2) with 256 in HFp6.
all: fold F in HFp6, HFSp6.
(* the frame and its shadow are not bytes the call may write *)
all: assert (HEF : forall a, (F <= a < F + 256 \/ SB + F / 8 <= a < SB + F / 8 + 32) ->
~ (C.bgs_ok s (F + 32) mx base w /\ s <= a < s + 34 * C.bgs_rows w))
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hbg := fresh "Hbg" in let Has := fresh "Has" in
intros a Ha [Hbg Has];
let Hbsw := fresh "Hbsw" in
pose proof (bt_bgs_bsw s (F + 32) al mx base w Haln Hw1 ltac:(lia) Hbw Hbg) as Hbsw;
let sb := fresh "sb" in let sn := fresh "sn" in let Hsbin := fresh "Hsbin" in let Hsblo := fresh "Hsblo" in let Hsbhi := fresh "Hsbhi" in
destruct (HSB Hbsw) as (sb & sn & Hsbin & Hsblo & Hsbhi);
let Hd := fresh "Hd" in
pose proof (sep_block_frame SEGS B LAWS ly S2 W _ _ sb sn 2 fpos HAR2 ltac:(rewrite Eab; exact Hsbin) Hfin2) as Hd;
let Hsb4096 := fresh "Hsb4096" in let Hsbceil := fresh "Hsbceil" in let Hsbapp := fresh "Hsbapp" in
destruct (al_blocks _ _ LAWS ly S W mem md sb sn HAR Hsbin) as (_ & Hsb4096 & Hsbceil & Hsbapp & _);
unfold zdisjoint in Hd; cbn [fst snd] in Hd; change (fs_frame_bytes 2) with 256 in Hd; fold F in Hd;
unfold C.bgs_rows in Has;
let Hrq := fresh "Hrq" in
assert (Hrq : req_size sn = sn) by (unfold req_size; destruct (Z.eqb_spec sn 0); lia);
rewrite Hrq in Hd, Hsbceil, Hsbapp;
revert Ha Has Hd Hsblo Hsbhi Hsb4096 Hsbceil Hsbapp HF8c HF8lo HF4096 HFceil C1 C3; clear;
unfold in_app, kLowShadowBeg, kHighMemBeg, SB; intros; lia).
all: clear HfinS2 EFA0.
all: reseat HS HJ6 HP6 [2; 3; 4; 5; 6]%nat AG ltac:(idtac; bt_kept HKc HJ6 AG HEF HFp6 Hfin2 F fpos).
all: fs_rwF HS E529 HFSp6.
all: rewrite Rra.
all: prreg HS (10%bv : bv 5) Ra0b.
(* ---- the flag byte; the values buffer's shadow back to 0xf8, the retired magic at F, the frame's shadow to
   0xf5, the flag store through F + 248 that releases the frame, the epilogue and the return ---- *)
all: assert (EFL6 : forall c p0, flag_addr ly6 c p0 = flag_addr ly c p0)
by (intros c p0; unfold flag_addr; pose proof Hly6 as (_ & _ & _ & _ & _ & EF6 & _); rewrite EF6; reflexivity).
all: destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ6) Hfin6) as (HFLpres6 & HFLown6 & HFLrng6).
all: rewrite EFL6 in HFLpres6, HFLown6, HFLrng6.
all: fold FL in HFLpres6, HFLown6, HFLrng6.
all: pose proof HFLrng6 as (_ & (HFL4096 & _ & HFLce)).
all: assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly6 S6 a) by (intros a Ha; exact (proj2 (HFp6 a Ha))).
all: add_flag_region HS AG E528 HFLpres6 HFLrng6 HFLown6 HnoF HnoF HnoF.
(* with the rows laid down: they are in a heap block the rest does not write *)
all: lazymatch goal with
| Hb : bsw_ok _ _ _ _ _ = true |- _ =>
destruct (HSB Hb) as (sb & sn & Hsbin & Hsblo & Hsbhi);
assert (Hsbin6 : In (sb, sn) (ablocks B ly6 S6)) by (rewrite Hab6, Eab; exact Hsbin);
destruct (al_blocks _ _ LAWS _ _ _ _ _ sb sn (proj1 HJ6) Hsbin6) as (_ & Hsb4096 & Hsbceil & Hsbapp & Hsbpres & _);
assert (Hrq : req_size sn = sn) by (unfold req_size; destruct (Z.eqb_spec sn 0); lia);
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ sb sn 2 fpos (proj1 HJ6) Hsbin6 Hfin6) as HdBF;
unfold zdisjoint in HdBF; cbn [fst snd] in HdBF; rewrite EFA6 in HdBF; change (fs_frame_bytes 2) with 256 in HdBF; fold F in HdBF;
rewrite Hrq in Hsbceil, Hsbapp, Hsbpres, HdBF;
assert (HnFL : ~ (s <= FL < s + 34 * (8 + 3 * w))) by (intros HFLs; exact (proj2 (Hsbpres FL ltac:(lia)) HFLown6));
assert (HKS : forall a, s <= a < s + 34 * (8 + 3 * w) -> aview SEGS (w_H W6) mem6 a = aview SEGS (w_H W6) mem6 a)
by (intros; reflexivity)
| _ => idtac end.
all: paj_run_flag_sh RUNF HS HJ6; [lia | bs_wrange AG fpos F EFA6 EFL6 Hsp1 FFS | flag0 E528 EFL6 |].
all: lazymatch goal with
| Hb : bsw_ok _ _ _ _ _ = true |- _ =>
upd_rngW HKS HFr ltac:(clear - Ha_rng Hsblo Hsbhi Hsb4096 Hsbceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E528 HnFL HdBF Hsblo Hsbhi Hsb4096 Hsbceil Hsbapp
HFL4096 HFLce HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3;
revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia))
| _ => idtac end.
all: prreg HS (1%bv : bv 5) R1.
all: prreg HS (10%bv : bv 5) R10.
all: lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
all: intros mat'; unfold bs_post, C.tb_reac_grant_build_sweep_post, apost_base.
all: lazymatch type of HJ6 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end.
all: split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 1%nat) by lia;
rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
all: split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ6|].
all: split; [apply aregs_preserved_eqs; creg HS AG EE|].
all: split; [pose proof HJ6 as (_ & _ & _ & _ & _ & Hfr6 & _); exact Hfr6|].
all: split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly6 S6); rewrite Hab6; exact Eab|].
all: split; [rewrite ES6, ES2, set_fs_set_fs; apply set_fs_free|].
all: split; [rewrite R10, <- Ra0b, Ha06, Hresv; rewrite ?Hbsw; reflexivity|].
all: lazymatch goal with
| Hb : bsw_ok _ _ _ _ _ = true |- _ =>
intros _; refine (garr8_aview_kept SEGS _ _ _ _ _ _ _ Hrows);
intros a Ha; apply HKS; rewrite length_map, bt_len_SWEEP in Ha by lia; lia
| _ => intros Hf; rewrite ?Hbsw in Hf; discriminate Hf end.
Qed.
End e.
End d.
End b.
