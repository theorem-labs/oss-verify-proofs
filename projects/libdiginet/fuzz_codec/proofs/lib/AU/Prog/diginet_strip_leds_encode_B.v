(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v, with its module paths and module names changed; 218 of its 266 lines of code are new or changed and 310 lines of the source are left out. *)
(* The image-B walk of diginet_strip_leds_encode (diginet_codec.c:247-255; image B 0x861d0, 30 instructions,
   frame 16) against lib/AU/Prog/CPgEncU.v's cdcU_sleds_specX, with leds_encode's image-B contract
   cdcU_leds_specX at 0x86248 as the premise.

   a0 = p, a1 = strip, a2 = bits, a3 = out. The prologue saves ra at sp - 8; that is the only store. Paths:
   - p = 0 (the test at 0x861dc is taken): a0 = -1, out untouched.
   - out = 0 (the test at 0x861e0): refuted by cenc_out's 0 < out (the atom fact of a3).
   - p mod 8 <> 0 (0x861e8, the UBSan check of the personality pointer; its trap is the `unimp` at 0x86234):
     refuted by the premise p mod 8 = 0, which is the alignment of p's atom fact, so the engine decides it.
   - the 1-byte load of p->strips at p + 17 (0x8620c) is checked against its shadow byte (0x861ec-0x86208,
     through 0x86238 / 0x8623c to the error path at 0x86244); pers_argA's cimg_range marks [p + 16, p + 20)
     usable in every state, which is the walk's shadow entry, so the check passes and the error path is not
     reached.
   - strip >= p->strips (the test at 0x86210 is taken): a0 = -11, out untouched.
   - else ra and sp are restored and the code jumps to leds_encode (0x8621c) with a0 = p, a1 = strip,
     a2 = bits, a3 = out: a tail call. CPgWalkTailU.v's tl_call makes leds_encode's post, taken at the jump
     state, the walk's post (same ra and sp as at the entry, the callee-saved registers kept, the walk's one
     store inside its window TB_sleds = TB_leds), and strip_leds_spec (Some d) strip bits = leds_spec d strip
     bits when strip < d_strips d. leds_encode's premises at the jump come from the walk's premises over the
     memory the walk kept (everything but its 16-byte frame).

   The GOT slot and the shadow-offset cell are read at 0x861ec-0x861f4 only; the walk then drops them and adds
   the byte p + 17, which the premises keep apart from the frame (lib/A/Prog/diginet_strip_leds_encode_A.v
   does the same at image A). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU CPgWalkCallU CPgWalkTailU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the Gallina result on each of the walk's paths ======================= *)
Lemma slb_spec_strips : forall d strip bits, d_strips d <= strip ->
strip_leds_spec (Some d) strip bits = (E_RANGE, None).
Proof.
intros d strip bits H. cbn [strip_leds_spec]. rewrite (proj2 (Z.leb_le (d_strips d) strip)) by lia. reflexivity.
Qed.
Lemma slb_spec_leds : forall d strip bits, strip < d_strips d ->
strip_leds_spec (Some d) strip bits = leds_spec d strip bits.
Proof.
intros d strip bits H. cbn [strip_leds_spec]. rewrite (proj2 (Z.leb_gt (d_strips d) strip)) by lia. reflexivity.
Qed.
Lemma slb_pow3 : 2 ^ 3 = 8. Proof. reflexivity. Qed.
Lemma slb_TB : TB_sleds = 4272. Proof. reflexivity. Qed.

(* ======================= the branch conditions, as Z facts ======================= *)
Section v. Context {fx : YK11.FPState}.
(* a 32-bit C argument in a register: its unsigned value *)
Lemma slb_U_s32 : forall (Ev : env) n v, ew Ev n = w64 (s32 v) -> 0 <= v < 2 ^ 32 ->
U Ev (SOff n 0) = (if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32)).
Proof.
intros Ev n v Hn Hv. unfold w64, s32 in Hn. rewrite U_SOff, Hn, Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl].
- rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
- replace (v - 2 ^ 32) with ((v + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (v + (2 ^ 64 - 2 ^ 32)) (2 ^ 64)) by lia.
  unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
(* `bgeu v, m` of a 32-bit C argument v against a byte m: v < m is decided on the plain values *)
Lemma slb_br_ge_byte : forall (Ev : env) n m v b, ew Ev n = w64 (s32 v) -> 0 <= v < 2 ^ 32 ->
ew Ev m = Z_to_bv 64 b -> 0 <= b < 256 ->
branch_taken BC_GEU (sv_denot Ev (SOff n 0)) (sv_denot Ev (SOff m 0)) = negb (v <? b).
Proof.
intros Ev n m v b Hn Hv Hm Hb. rewrite branch_geu_U, (slb_U_s32 Ev n v Hn Hv).
rewrite (cw_U_atom0 Ev m b Hm ltac:(lia)).
destruct (Z.ltb_spec v (2 ^ 31)) as [Hl|Hl]; [reflexivity|].
destruct (Z.ltb_spec (v + (2 ^ 64 - 2 ^ 32)) b) as [H1|H1]; destruct (Z.ltb_spec v b) as [H2|H2];
first [reflexivity | lia].
Qed.
(* `beqz p` of the personality pointer *)
Lemma slb_br_eq0 : forall (Ev : env) n v, ew Ev n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot Ev (SOff n 0)) (sv_denot Ev (SLit 0)) = (v =? 0).
Proof.
intros Ev n v Hn Hv. rewrite branch_eq_U, (cw_U_atom0 Ev n v Hn Hv), U_SLit.
rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
End v.

(* ======================= the walk's state ======================= *)
(* the personality's strip count at p + 17 (atom 33) *)
Definition slb_pers : YP09.region :=
YP09.mkRegion (Some 10%nat) 17 18 0 0 [YP09.mkChunk 17 (CVal 1 (SOff 33 0))].
(* the shadow of the four personality bytes *)
Definition slb_SH : list shent := [mkSHE 10 16 20].
(* p is 8-aligned and not 0 (so the null and alignment tests are decided), out is not 0, the strip count is a
   byte *)
Definition slb_AF : list (nat * afact) :=
[(10%nat, mkAF 8 (2 ^ 47 - 24) 3); (13%nat, mkAF 1 (2 ^ 47 - 33) 0); (33%nat, mkAF 0 255 0)].

(* an atom's value in the env of a stop: strip the run's fresh atoms, then the walk's own equation *)
Ltac slb_ew0 := rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; eassumption.

(* ======================= the walk ======================= *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Theorem diginet_strip_leds_encode_B_holds :
  cdcU_leds_specX tfibsegs B MT 0x86248 -> cdcU_sleds_specX tfibsegs B MT 0x861d0.
Proof using MTL TL LAWS ML.
intros LEDS. unfold cdcU_leds_specX in LEDS. unfold cdcU_sleds_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p strip bits out before
  HE H10 Hpers Hp8 Hstrip Hbits H13 Ho4 HOUT Hobj Hdisj Hnfr.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_sleds HE
  ltac:(rewrite slb_TB; lia)) as (Hceil & H47 & H46 & _ & Hpres).
assert (H46' : 2 ^ 46 + 4272 <= spZ regs) by (rewrite <- slb_TB; exact H46).
assert (Hwlo' : sp0 - STK <= spZ regs - 4272) by (rewrite <- slb_TB; exact Hwlo).
pose proof HOUT as (Hcdst & Hbef & Hlen).
pose proof Hcdst as (Hout0 & Hout63 & Htdst & Htwr & Hora & Hohull & Hoam & Howin).
assert (Ho47 : out + 32 <= 2 ^ 47 - 1)
  by (unfold amem_range in Hoam; rewrite C4, C5 in Hoam; destruct Hoam as [Hl | [_ Hh]]; lia).
assert (Howin' : out + 32 <= spZ regs - 16 \/ spZ regs <= out)
  by (unfold coff_win in Howin; rewrite slb_TB in Howin; lia).
change (w64 out) with (Z_to_bv 64 out) in H13.
change (w64 p) with (Z_to_bv 64 p) in H10.
pose proof Hstrip as (Rstrip & Estrip). pose proof Hbits as (Rbits & Ebits).
(* no byte of out is a byte of the image *)
assert (HEIMG : forall a, cenc_wr out a -> in_img tfibsegs a -> False).
{ intros a Ha Him. unfold cenc_wr in Ha.
  exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a (proj1 HJ0) Htdst Ha Him). }
destruct pd as [d|].
- (* ======================= the personality is present ======================= *)
  pose proof Hpers as (Hp0 & Hp63 & Rdev & Rstrips & Rchars & Rcounter & Hpg & Hcimg).
  pose proof Hcimg as (Hq0 & Hn0 & Hq63 & Hpam & Hpwin & Himgb & Husable).
  assert (Hp47 : p + 20 <= 2 ^ 47 - 1)
    by (unfold amem_range in Hpam; rewrite C4, C5 in Hpam; destruct Hpam as [Hl | [_ Hh]]; lia).
  assert (Hpwin' : p + 20 <= spZ regs - 16 \/ spZ regs <= p + 16)
    by (unfold coff_win in Hpwin; rewrite slb_TB in Hpwin; lia).
  destruct (Husable lyc Sc W memc mdc (proj1 HJ0)) as (Hpra & Hphull).
  set (xs := [d_strips d]).
  assert (X33 : ew (Ereg regs (cw_extra xs)) 33 = Z_to_bv 64 (d_strips d)) by exact (cw_ew_x regs xs 0).
  assert (Hp8r : 8 <= p <= 2 ^ 47 - 24)
    by (pose proof (Z.div_mod p 8 ltac:(lia)) as Hd; rewrite Hp8, Z.add_0_r in Hd; lia).
  assert (HAF : atoms_ok (Ereg regs (cw_extra xs)) slb_AF).
  { unfold slb_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), (ew_Ereg_nat regs _ 13 13%bv eq_refl), H10, H13, X33.
    rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r, slb_pow3. repeat split; lia. }
  pose proof (cw_entry_base_af B TL LAWS 0x861d0 16 xs slb_AF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    regs TB_sleds HE ltac:(rewrite slb_TB; lia) ltac:(vm_compute; reflexivity) HAF) as HS.
  remember (Ereg regs (cw_extra xs)) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra xs)) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = w64 (s32 strip)) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Estrip).
  assert (E12 : ew E 12 = w64 (s32 bits)) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact Ebits).
  assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (E33 : ew E 33 = Z_to_bv 64 (d_strips d)) by (subst E; exact X33).
  clear HEE. clearbody xs.
  assert (SHOK : sh_ok tfibsegs CW_Bx slb_SH E (mrestrict (w_H W) memc)).
  { unfold slb_SH. apply Forall_cons; [|apply Forall_nil].
    exact (cw_shent_ra_off W memc E 10 p 16 4 Hpra Hpam ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E10 E32). }
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x861d0) with (Z_to_bv 64 0x861d0).
  (* 0x861d0-0x86208: the save of ra, the two null tests and the alignment test (decided by the atom facts),
     the shadow offset through the .got slot and its cell, and the shadow byte of p + 17 (the walk's shadow
     entry decides the test); the run stops at the load of p + 17 at 0x8620c, which no region holds yet *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  (* the personality's bytes are off the save slot, so they are what they were *)
  assert (HPG : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms)) (p + 16)
    [d_dev d; d_strips d; d_chars d; d_counter d]).
  { apply (tl_garr8_kept W memc (ms_mem ms) (p + 16) _ Hpg).
    intros a Ha. cbn [length] in Ha. apply KE; lia. }
  (* the shadow offset is held in a register now and the cells are dead: drop the .got slot and the cell (the
     personality may lie on either of them), and add the byte p + 17 *)
  cw_drop_gb.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv ?msv |- _ =>
    let E10v := fresh "E10v" in let E33v := fresh "E33v" in let B2v := fresh "B2v" in
    let Hpok := fresh "Hpok" in let HD := fresh "HD" in let HS2 := fresh "HS" in
    assert (E10v : ew Ev 10 = Z_to_bv 64 p) by slb_ew0;
    assert (E33v : ew Ev 33 = Z_to_bv 64 (d_strips d)) by slb_ew0;
    assert (B2v : bv_unsigned (ew Ev 2) = spZ regs) by slb_ew0;
    assert (Hpok : region_ok tfibsegs Ev (mrestrict (w_H W) (ms_mem ms)) slb_pers);
    [ unfold region_ok, slb_pers;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite E10v, unsigned_lit_small by lia;
      split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val tfibsegs Ev _ p 17 1 (SOff 33 0) (d_strips d));
      [cbn [sv_denot]; rewrite E33v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
      let HV := fresh "HV" in pose proof (proj1 (HPG 1%nat ltac:(cbn; lia))) as HV;
      cbn [nth] in HV; change (Z.of_nat 1) with 1 in HV;
      replace (p + 16 + 1) with (p + 17) in HV by lia; exact HV
    | ];
    assert (HD : all_disjoint Ev slb_pers (ss_mem ssv));
    [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, slb_pers;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E10v, B2v, unsigned_lit_small by lia;
      split; [lia | exact I]
    | ];
    pose proof (ast_ok_add_region tfibsegs Ev ssv msv slb_pers HS eq_refl Hpok HD) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS HD Hpok E10v E33v B2v; rename HS2 into HS end.
  (* 0x8620c: the load of the strip count; stop at 0x86210 `bgeu strip, strips` *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb2.
  all: lazymatch type of Hb2 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
       rewrite (slb_br_ge_byte Ev 11 33 strip (d_strips d) ltac:(slb_ew0) ltac:(lia) ltac:(slb_ew0) ltac:(lia)) in Hb2 end.
  + (* strip >= the strip count: a0 = -11, out untouched *)
    apply negb_true_iff, Z.ltb_ge in Hb2.
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG)
                    ltac:(idtac; intros a Hz; left; cbv beta in Hz; rewrite slb_TB; lia))
            ltac:(idtac; rewrite (slb_spec_strips d strip bits ltac:(lia)); unfold cenc_res; cbn [fst snd cmd_outZ]; split;
                  [rewrite R10; unfold w64, E_RANGE; apply bv_eq; vm_compute; reflexivity
                  | apply (tl_garr8_kept W memc _ out before Hbef);
                    intros a Ha; rewrite Hlen in Ha; apply KE; lia]).
  + (* strip < the strip count: ra and sp restored, the jump to leds_encode at 0x8621c *)
    apply negb_false_iff, Z.ltb_lt in Hb2.
    cw_run_to cw_awr_stk 0x86248. cw_keep cw_kwr_stk.
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ss (restrict (w_H W) ?ms) |- SRr _ _ (mkCfg ?ms ?mdd) _ =>
      let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in let R4 := fresh "R4" in
      let R10 := fresh "R10" in let R11 := fresh "R11" in let R12 := fresh "R12" in let R13 := fresh "R13" in
      let Rsp := fresh "Rsp" in
      rreg HS (1%bv : bv 5) R1; rreg HS (2%bv : bv 5) R2; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
      rreg HS (10%bv : bv 5) R10; rreg HS (11%bv : bv 5) R11; rreg HS (12%bv : bv 5) R12;
      rreg HS (13%bv : bv 5) R13;
      assert (Rsp : spZ (ms_regs ms) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity);
      eapply (tl_call B MT LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_sleds (cenc_wr out)
        (cenc_res tfibsegs out before (strip_leds_spec (Some d) strip bits)) Ev ss ms mdd TB_leds
        (cenc_res tfibsegs out before (leds_spec d strip bits)));
      [ exact HS | reflexivity | exact HJ0 | exact HJ
      | let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
          | eapply same_io_trans; [| apply same_io_materialized; eassumption]; kio] in kio
      | rewrite R1, E1; reflexivity
      | eapply aregs_preserved_of_st_ok; [exact HS | env_agree_chain HAE | vm_compute; reflexivity]
      | exact Rsp | exact Hceil | exact H47 | exact Hwlo | exact Hwhi
      | split; [unfold TB_leds, TB_sysex, ESTACK; lia | apply Z.le_refl]
      | exact HEIMG
      | intros a Ha Hw _; apply KE; [exact Ha | intros Hz; apply Hw; rewrite slb_TB; lia]
      | intros W3 mem3 regs3 HR3; rewrite (slb_spec_leds d strip bits ltac:(lia)); exact HR3
      | ];
      lazymatch goal with |- SRr _ _ (cfg_at _ ?pc _ _ _) _ =>
        let pc' := eval vm_compute in pc in change pc with pc' end;
      eapply (LEDS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) mdd k (ms_regs ms) d p strip bits out before);
      [ eapply (cpw_entry B);
        [ exact HJ | rewrite R1, E1; exact Hra | unfold raZ; rewrite R1, E1; exact Hra4
        | rewrite R3, E3; exact Hgp | rewrite R4, E4; exact Htp
        | rewrite Rsp; exact Hal16 | rewrite Rsp; exact Hwlo | rewrite Rsp; exact Hwhi
        | exact Hev | apply Permutation_refl | exact Hlive ]
      | rewrite R10, E10; reflexivity
      | rewrite Rsp; apply (tl_pers_kept B W memc (ms_mem ms) _ _ p d Hpers); intros a Ha; apply KE; lia
      | exact Hp8
      | rewrite R11, E11; unfold s32; rewrite (proj2 (Z.ltb_lt strip (2 ^ 31))) by lia; reflexivity
      | lia
      | split; [exact Rbits | rewrite R12, E12; reflexivity]
      | rewrite R13, E13; reflexivity
      | exact Ho4
      | rewrite Rsp; apply (tl_out_kept B STK sp0 FP ly S lyc Sc own W memc (ms_mem ms) (spZ regs) TB_leds out before
          (spZ regs - 16) (spZ regs) HOUT KE); [lia | exact Howin' | intros a Ha; exact (HEIMG a Ha)]
      | exact Hobj | exact Hdisj | exact Hnfr ]
    end.
- (* ======================= the personality is NULL ======================= *)
  cbn [pers_argA] in Hpers. subst p.
  pose proof (cw_entry_base B TL LAWS 0x861d0 16 (@nil Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    TB_sleds HE ltac:(rewrite slb_TB; lia) ltac:(vm_compute; reflexivity)) as HS.
  remember (Ereg regs (cw_extra [])) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by (apply Forall_nil).
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x861d0) with (Z_to_bv 64 0x861d0).
  (* 0x861d0-0x861d8: the save of ra and a4 = -1; stop at 0x861dc `beqz p` *)
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  cw_branch Hb0.
  all: lazymatch type of Hb0 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
       rewrite (slb_br_eq0 Ev 10 0 ltac:(slb_ew0) ltac:(lia)) in Hb0 end.
  + (* taken (p = 0): the return with a0 = -1 and out untouched *)
    cw_run cw_awr_stk. cw_keep cw_kwr_stk.
    cw_leaf ltac:(idtac; cw_kept HJ0 KE ltac:(exact HEIMG)
                    ltac:(idtac; intros a Hz; left; cbv beta in Hz; rewrite slb_TB; lia))
            ltac:(idtac; cbn [strip_leds_spec]; unfold cenc_res; cbn [fst snd cmd_outZ]; split;
                  [rewrite R10; unfold w64, E_ARG; apply bv_eq; vm_compute; reflexivity
                  | apply (tl_garr8_kept W memc _ out before Hbef);
                    intros a Ha; rewrite Hlen in Ha; apply KE; lia]).
  + (* not taken: p <> 0, which the premise refutes *)
    exfalso. cbn in Hb0. discriminate Hb0.
Qed.
End d.
End b.
