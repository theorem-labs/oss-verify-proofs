(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PvB_NA.v, with its module paths and module names changed; 499 of its 552 lines of code are new or changed and 906 lines of the source are left out. *)
(* fuzz_preset image B' (asan-ubsan, #102), parse_value 0x8637c, segment D (the DISPATCH): the LITERAL
   CALL ARM ('t' / 'f' / 'n'). From the callee's entry state (PvB_D_Call.v pvd_cs at `jal literal`, B 0x86644) the call
   is the tliteral_specX (the kit's lib/A/PRH_FnReader.v blob c30f1da6a2d1: the ledger with the #102
   statics most / own, kept; fpre with frm_zero at the entry float state, which before strtod is parse_value's fx0,
   rd_pre's first conjunct) through YCbqGcallW.v's aj_call_xW, with the callee's window from its sp Y up to sp0 + e
   and its footprint [(q, q + 8); (v, v + 4)]; back at 0x86648 a fresh symbolic state runs the one instruction
   `mv s5, a0` to the shared exit 0x8664c, and the exit cut pv_at_exit is built: the frame kept by the callee's window
   clause and journal, the post's memory part by PvB_D_Lit.v pvD_Qm_lit (with the room post inside it: no model
   event, so PvB_Room.v rp_nil over pv_reader0's room keep, carried by the post's `S' = S`), the memory normal form by
   the post's m-form keep (fpostWm, PRH_Base.v fQmn) from the call state's (pvd_cs) and the exit stretch's runner twin
   (paj_run_to_x_inv). fpre's return-address bound at the call is the jal's return slot (PvB_D_Kit.v
   pvd_ret_lt_ceil).
   The words literal compares: the MARKED image fact LITCS gives cstr_ok for each of the three .rodata words; the
   bytes from the NUL to the next 8-byte boundary (the text's slack) are the bytes the memory shows there (cstr_ok
   makes them visible), so the slack, its alignment, the 2 ^ 63 bound and the place below literal's stack window
   follow from cstr_ok and literal's afn_pre_x.
   Numerals: 56 / 4 / 8 / 24 node, type, word and cursor sizes, 64 the class-0 fake frame, 176 / 160 the frame
   (LENGTH); 116 / 102 / 110 the dispatch bytes (WORD); 2 ^ 63, 2 ^ 64 range bounds; 16880 / 8704 stack-budget bounds
   (DERIVED from STK_parse_value / STK_literal); 0 / -1 the result codes.
   Rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model PvB_D_Lit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_D_Kit PvB_D_Call.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.
(* YK06 declares a concrete alloc_ceiling; every kit statement here reads the run's ceiling YM05.alloc_ceiling *)
#[local] Abbreviation alloc_ceiling := YM05.alloc_ceiling.

(* the symbolic state at literal's return 0x86648: every register its own atom, no region, no fact; the stretch
   (`mv s5, a0`) reads no shadow, so the shadow span is empty *)
Definition pvc_ss : sstate := mkSS AF_pv_lit_ret sr_atoms [] None (mkFacts [] [] []).
Definition PVC_Bx : sv := SLit SHADOW_OFF.
Definition PVC_Bspan : Z * Z := (0, 0).

(* a kept register (aregs_preserved's `Z_to_bv 5 r` form) read at its literal index (PvB_A.v pva_getr_lit) *)
Lemma pvc_getr_lit : forall (regs regs' : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
  getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z) -> getr regs' r = getr regs r.
Proof. intros regs regs' r z Hr H. subst z. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac pvc_keep P rlit z := exact (pvc_getr_lit _ _ rlit z eq_refl (P z ltac:(unfold acallee_saved; lia))).
(* one conjunct of a hypothesis, found by its type (the cut's conjunct order may move) *)
Ltac pvc_pick H := clear - H; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end; assumption.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation PSTX := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ---- Section hypotheses ---- *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TLIT : tliteral_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK.
(* MARKED image fact, discharged at PI_prog_B: no read-only byte is one of alloc.c's statics (S1ImgB.v pst_not_ro_B) *)
Hypothesis RONP : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) PSTX.
(* MARKED image fact, discharged at PI_prog_B; the record gap V3 (lib/A/PRH_FnParse.v:87) *)
Hypothesis LITCS : forall ly S Hp W mem md c, ARx ly S Hp W mem md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> (c = 116 \/ c = 102 \/ c = 110) ->
  cstr_ok W mem (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c).

(* ---- helpers ---- *)
(* a read-only byte is an image byte (PvB_A.v pva_ro_img) *)
Lemma pvc_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* blocks_bytes reads the blocks' sizes only (PvB_A.v pva_bb_ab) *)
Lemma pvc_bb_ab : forall ly S, blocks_bytes S = fold_right (fun b acc => snd b + acc) 0 (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.
(* garr8 over an append *)
Lemma pvc_garr8_app : forall (m : word -> option byte) a l1 l2,
  garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr].
  replace (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) with (a + Z.of_nat j) in Hv by lia.
  split; assumption.
Qed.
(* the slack of a C string the memory shows: the bytes from its NUL to the next 8-byte boundary are visible (cstr_ok's
   last conjunct), so they are some byte list of that length *)
Lemma pvc_slack : forall (W : world SEGS) mem w cw, cstr_ok W mem w cw ->
  exists sl, garr8 SEGS (rdW W mem) w (cw ++ 0 :: sl) /\
    Z.of_nat (length sl) = (- (w + Z.of_nat (length cw) + 1)) mod 8.
Proof.
intros W mem w cw ((Hg & _) & _ & _ & _ & _ & _ & _ & Htail).
pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length cw) + 1)) 8 ltac:(lia)) as Hb.
set (n := Z.to_nat ((- (w + Z.of_nat (length cw) + 1)) mod 8)).
set (f := fun i : nat => match mbyte SEGS (rdW W mem) (w + Z.of_nat (length cw) + 1 + Z.of_nat i) with
  | Some b => bv_unsigned b | None => 0 end).
exists (map f (seq 0 n)). split.
- replace (cw ++ 0 :: map f (seq 0 n)) with ((cw ++ [0]) ++ map f (seq 0 n))
    by (rewrite <- app_assoc; reflexivity).
  apply pvc_garr8_app; [exact Hg|].
  intros j Hj. rewrite length_map, length_seq in Hj.
  assert (Hj' : Z.of_nat j < (- (w + Z.of_nat (length cw) + 1)) mod 8).
  { apply Nat2Z.inj_lt in Hj. unfold n in Hj. rewrite Z2Nat.id in Hj by lia. exact Hj. }
  rewrite (nth_indep (map f (seq 0 n)) 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. cbn [Nat.add].
  assert (Ea : w + Z.of_nat (length (cw ++ [0])) + Z.of_nat j = w + Z.of_nat (length cw) + 1 + Z.of_nat j)
    by (rewrite length_app; cbn [length]; lia).
  rewrite Ea.
  assert (Hvis : aview SEGS (w_H W) mem (w + Z.of_nat (length cw) + 1 + Z.of_nat j) <> None).
  { apply Htail. clear - Hj' Hb. lia. }
  unfold f. unfold aview in Hvis. revert Hvis.
  destruct (mbyte SEGS (rdW W mem) (w + Z.of_nat (length cw) + 1 + Z.of_nat j)) as [b|] eqn:Hbyte;
    intros Hvis; [|exfalso; apply Hvis; reflexivity].
  cbv beta iota.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  apply YI01.val_mem1_of_mbyte; [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hbyte.
- rewrite length_map, length_seq. unfold n. rewrite Z2Nat.id by lia. reflexivity.
Qed.
(* pv_frame across a change of world and memory that keeps the frame's bytes' views and their presence *)
Lemma pvc_frame_trW : forall regs0 sp0 Y fa fl shb (W W' : world SEGS) mem mem',
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64) -> apresent (w_H W') mem' a) ->
  pv_frame regs0 sp0 Y fa fl shb W mem -> pv_frame regs0 sp0 Y fa fl shb W' mem'.
Proof.
intros regs0 sp0 Y fa fl shb W W' mem mem' HK HP (HYr & HY32 & HPR & Vsav & V48 & Vm & Vd & Vp & Vf & HPf & Hl & G).
assert (HKm : forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
  mbyte SEGS (rdW W' mem') a = mbyte SEGS (rdW W mem) a).
{ intros a Ha. apply (mbyte_of_aview SEGS). exact (HK a Ha). }
assert (VT : forall a n v, (forall kk, (kk < n)%nat -> Y <= a + Z.of_nat kk < sp0 \/ fa <= a + Z.of_nat kk < fa + 64) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W' mem') a n v).
{ intros a n v Hr Hv kk Hk. rewrite HKm; [exact (Hv kk Hk)|]. destruct (Hr kk Hk) as [H1|H1]; [left|right; left]; exact H1. }
unfold pv_frame. split; [exact HYr|]. split; [exact HY32|].
split; [intros a Ha; apply HP; left; exact Ha|].
split.
{ rewrite Forall_forall in Vsav |- *. intros [o r] Hin. apply VT; [|exact (Vsav _ Hin)].
  intros kk Hk. left. cbn [fst].
  assert (Ho : -104 <= o <= -8).
  { unfold pv_saved in Hin. repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin. }
  lia. }
split; [apply VT; [intros kk Hk; left; lia | exact V48]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vm]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vd]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vp]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vf]|].
split; [intros a Ha; apply HP; right; exact Ha|].
split; [exact Hl|].
intros j Hj. destruct (G j Hj) as [Gv Gr]. split; [|exact Gr].
intros kk Hk. rewrite HKm; [exact (Gv kk Hk)|]. right; right. rewrite Hl in Hj. cbn in Hk. lia.
Qed.

(* THE PACKAGING at the exit: literal's post (its prefixb split, v's bytes [v + 4, v + 56) kept) at a memory, carried
   to a pointwise-equal one, is pv_Qm with the code literal returned *)
Lemma pvc_Qm : forall en c y pos lyc Sc (Wc : world SEGS) memc ly' S' (W' : world SEGS) mem' mem'',
  pv_pre B ARx en -> PjGrammar.skip (pe_rest en) = c :: y -> (c = 116 \/ c = 102 \/ c = 110) ->
  pv_reader0 B en pos (pe_text en + pe_len en - Z.of_nat (length (c :: y))) lyc Sc Wc memc ->
  (forall x, mrestrict (w_H W') mem'' x = mrestrict (w_H W') mem' x) ->
  (room_live_cf Sc -> room_live_cf S') -> ablocks B ly' S' = ablocks B lyc Sc -> frames S' = frames Sc ->
  prh_ledger B ly' S' (pe_Hp en) W' mem' (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
    (pe_own en) ->
  rp_keep (pe_S en) S' -> YGcfSecsStep.secs_same (pe_S en) S' ->
  (if PjGrammar.prefixb (pvd_lit_word c)
        (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y))))
   then
     pj_in_okR SEGS (rdW W' mem') (pe_q en) (pe_text en) (pe_len en)
       (pe_text en + pe_len en - Z.of_nat (length (c :: y)) + Z.of_nat (length (pvd_lit_word c)))
       (Z.of_nat (pe_d en)) (pe_tb en) /\
     val_mem SEGS (rdW W' mem') (pe_v en) 4 (pvd_lit_ty c)
   else
     pj_in_okR SEGS (rdW W' mem') (pe_q en) (pe_text en) (pe_len en)
       (pe_text en + pe_len en - Z.of_nat (length (c :: y))) (Z.of_nat (pe_d en)) (pe_tb en) /\
     (forall a, pe_v en <= a < pe_v en + 4 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a)) ->
  (forall a, pe_v en + 4 <= a < pe_v en + 56 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  pv_Qm B en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en)))
    (if PjGrammar.prefixb (pvd_lit_word c)
          (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y))))
     then 0 else -1)
    ly' S' (pe_Hp en) W' mem''.
Proof.
intros en c y pos lyc Sc Wc memc ly' S' W' mem' mem'' HPRE Hsk Hc HR0 EQ Hroom Eab Efr HLED HPOS HSEC Hpost Hkeep.
assert (EA : forall a, aview SEGS (w_H W') mem'' a = aview SEGS (w_H W') mem' a)
  by (intros a; apply pvl_aview_ext; exact EQ).
assert (Hbb : blocks_bytes S' = blocks_bytes Sc) by (rewrite (pvc_bb_ab ly' S'), (pvc_bb_ab lyc Sc), Eab; reflexivity).
apply (pvD_Qm_lit B ARx LAWS en pos (pe_text en + pe_len en - Z.of_nat (length (c :: y))) lyc Sc Wc memc ly' S'
  (pe_Hp en) W' mem'' c (pvd_lit_ty c)
  (if PjGrammar.prefixb (pvd_lit_word c)
        (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y))))
   then 0 else -1)
  y (pvd_lit_word c) (if c =? 116 then PjTree.JTrue else if c =? 102 then PjTree.JFalse else PjTree.JNull) HPRE).
- rewrite Hsk. reflexivity.
- exact Hsk.
- exact HR0.
- destruct Hc as [-> | [-> | ->]]; [left | right; left | right; right]; repeat split; try reflexivity.
- exact Hroom.
- reflexivity.
- exact Eab.
- exact Efr.
- exact Hbb.
- eapply pvl_prh_ledger_ext; [exact EQ | exact HLED].
- exact HPOS.
- exact HSEC.
- revert Hpost.
  destruct (PjGrammar.prefixb (pvd_lit_word c)
    (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y)))));
    intros (Hin' & Hv'); (split; [reflexivity|]).
  + split; [eapply pvl_pj_in_okR_ext; [exact EQ | exact Hin'] | eapply pvl_val_mem_ext; [exact EQ | exact Hv']].
  + split; [eapply pvl_pj_in_okR_ext; [exact EQ | exact Hin'] | intros a Ha; rewrite EA; exact (Hv' a Ha)].
- intros a Ha. rewrite EA. exact (Hkeep a Ha).
Qed.

(* ---- THE ARM ---- *)
Lemma pvd_call_lit : pvd_lit_goal B ARx.
Proof.
unfold pvd_lit_goal.
intros en c y Y fa fl pos lyc Sc k W' regs mem mdc HPRE Hsk Hc HCS R10 R11 R12 R13 HKX.
unfold pvd_kx in HKX.
destruct HCS as (HKR & R9 & R19 & R20 & R24 & R1 & HBODY & HCHAIN & HRD0 & _ & _ & HMNc).
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HFRM as (HYr & HY32 & _).
(* the entry premises, each found by its type *)
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; pvc_pick HPRE).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; pvc_pick HPRE).
unfold fpre in HFPRE.
assert (HAFN : afn_pre_x SEGS B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en)
  (pe_md en) (pe_ch en)) by pvc_pick HFPRE.
assert (HRO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (pe_W en)) (pe_mem en))) by pvc_pick HFPRE.
unfold afn_pre_x in HAFN.
assert (Hgp : getr (pe_regs en) 3 = w64 (as_gp B)) by pvc_pick HAFN.
assert (Htp : getr (pe_regs en) 4 = w64 (as_tp B)) by pvc_pick HAFN.
assert (Hstk0 : astk_ok (pe_STK en) (pe_ly en) (spZ (pe_regs en))) by pvc_pick HAFN.
unfold rd_pre in HRDP.
assert (Hfrm0 : YK0o.frm_zero (@YK11.fp_csr fx0)) by pvc_pick HRDP.
assert (Hwin : fwin (pe_ly en) (pe_W en) (pe_regs en) (pe_mem en) (pe_e en)) by pvc_pick HRDP.
assert (Hqlo : spZ (pe_regs en) <= pe_q en) by pvc_pick HRDP.
assert (Hqhi : pe_q en + 24 <= spZ (pe_regs en) + pe_e en) by pvc_pick HRDP.
assert (Hnode : prhPv_node B (pe_STK en) (pe_e en) (pe_ly en) (pe_S en) (pe_W en) (pe_regs en) (pe_mem en)
  (pe_Lam en) (pe_v en)) by pvc_pick HRDP.
assert (Hqv : pe_q en + 24 <= pe_v en \/ pe_v en + 56 <= pe_q en) by pvc_pick HRDP.
(* rd_pre's text / node apartness is guarded by 0 < len (the batch kit); the arm reads a byte at p1 < end, so it holds below *)
assert (Htv0 : 0 < pe_len en -> pe_text en + pe_len en <= pe_v en \/ pe_v en + 56 <= pe_text en) by pvc_pick HRDP.
assert (Hvwin : pe_v en + 56 <= spZ (pe_regs en) \/ spZ (pe_regs en) + pe_e en <= pe_v en) by pvc_pick HRDP.
assert (HLED0 : prh_ledger B (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_Lam en) (pe_peak en)
  (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en)) by pvc_pick HRDP.
clear HRDP HFPRE HAFN.
unfold prhPv_node in Hnode.
assert (Hv4096 : 4096 <= pe_v en) by pvc_pick Hnode.
assert (Hv8 : pe_v en mod 8 = 0) by pvc_pick Hnode.
assert (Hvat : prhReader_at B (pe_ly en) (pe_S en) (pe_Lam en) (pe_regs en) (pe_e en) (pe_v en) 56) by pvc_pick Hnode.
clear Hnode.
pose proof Hwin as (He0 & He16 & Hetop & _).
(* the C1 reader facts, each found by its type (the cut's conjunct order may move) *)
assert (Hfrs : frames Sc = (0, pos) :: frames (pe_S en)) by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
assert (Habl : ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en)) by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
assert (HCUR : pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en)
  (pe_text en + pe_len en - Z.of_nat (length (c :: y))) (Z.of_nat (pe_d en)) (pe_tb en))
  by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
assert (HSRC : src_rd W' mem (pe_text en) (pe_tb en)) by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
assert (HHOME : prhReader_home B lyc Sc (pe_Hp en) (pe_Lam en) (pe_text en) (pe_len en))
  by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
assert (HVRA : range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF (pe_v en) 56)
  by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
(* the text is not empty: the C1 cursor p1 = end - |c :: y| lies in [text, text + len] *)
assert (Htv : pe_text en + pe_len en <= pe_v en \/ pe_v en + 56 <= pe_text en).
{ apply Htv0. pose proof HCUR as (_ & _ & _ & _ & _ & _ & _ & Hp1r & _).
  assert (Hl1 : 1 <= Z.of_nat (length (c :: y))) by (cbn [length]; lia).
  clear - Hp1r Hl1. lia. }
clear Htv0.
assert (HLEDc : prh_ledger B lyc Sc (pe_Hp en) W' mem (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en)
  (pe_most en) (pe_own en)) by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
(* the room keep from entry to the call state (pv_reader0's last conjunct) *)
assert (HRPc : rp_keep (pe_S en) Sc) by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
(* the hull meters kept from entry to the call state (pv_reader0's secs_same) *)
assert (HSECc : YGcfSecsStep.secs_same (pe_S en) Sc) by (unfold pv_reader0 in HRD0; pvc_pick HRD0).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _ & _ & _ & Hstkj & _).
pose proof Hly as (_ & _ & _ & _ & _ & EFl & _ & _ & _ & Eloc & Ehic & _).
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hstkj as (_ & _ & _ & _ & Hshij & _).
pose proof asan_consts as (CC1 & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
(* ---- bounds ---- *)
assert (HSTKv : 16880 <= pe_STK en).
{ assert (E : pe_STK en = Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560) by reflexivity.
  rewrite E. clear. lia. }
assert (HSL : 0 <= STK_literal (PI := PIB) <= 8704) by (vm_compute; split; congruence).
assert (HY0 : 0 <= Y < 2 ^ 64) by (clear - HYr Hceil Hslo HSTK0 Hshi H47 CC1; lia).
assert (HspY : spZ regs = Y) by (unfold spZ; rewrite R2; apply unsigned_lit_small; clear - HY0; lia).
assert (Hsp64 : 0 <= pe_sp en < 2 ^ 64) by (clear - HYr Hceil Hslo HSTK0 Hshi H47 CC1; lia).
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
assert (EFc : forall c0 p0, frame_addr lyc c0 p0 = frame_addr (pe_ly en) c0 p0)
  by (intros; unfold frame_addr; rewrite EFl; reflexivity).
(* where the node lies: a block of the C1 state or a fake frame of the entry state (rd_pre takes it out of the
   caller's window) *)
assert (HVLOC : (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= pe_v en /\ pe_v en + 56 <= b + req_size m) \/
  (exists cid p', In (cid, p') (frames (pe_S en)) /\ frame_addr lyc cid p' <= pe_v en /\
     pe_v en + 56 <= frame_addr lyc cid p' + fs_frame_bytes cid)).
{ destruct Hvat as [(a0 & k0 & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
  - left. pose proof HLED0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
    destruct (HF (a0, k0) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
    exists (a0 - cf_head), (k0 + cf_head). rewrite Habl. split; [exact Hab0|].
    pose proof (@cf_head_nonneg cp). clear - Hk0 H1 H2 H. unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
  - left. exists b, m. rewrite Habl. split; [exact Hin|]. clear - H1 H2. unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - right. exists cid, p'. rewrite !EFc. auto.
  - exfalso. unfold pe_sp in Hvwin. clear - H1 H2 Hvwin. destruct Hvwin; lia. }
assert (HinFr : forall cid p', In (cid, p') (frames (pe_S en)) -> In (cid, p') (frames Sc))
  by (intros cid p' Hin; rewrite Hfrs; right; exact Hin).
assert (Hvlow : pe_v en + 56 <= alloc_ceiling /\ in_app (pe_v en) 56).
{ destruct HVLOC as [(b & m & Hin & H1 & H2) | (cid & p' & Hin & H1 & H2)].
  - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hcb & Happ & _).
    split; [clear - Hcb H2; lia | apply (in_app_sub _ _ _ _ Happ); clear - H1 H2; lia].
  - destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR (HinFr _ _ Hin)) as (_ & Hcb & Happ).
    pose proof (fs_frame_bytes_nonneg cid).
    split; [clear - Hcb H2; lia | apply (in_app_sub _ _ _ _ Happ); clear - H1 H2; lia]. }
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HinF) as (Hfa0 & Hfac & Hfapp).
rewrite <- Efa, Efb in Hfac, Hfapp. rewrite <- Efa in Hfa0.
(* the node is apart from the fake frame and from the fake frame's shadow *)
assert (HDFA : fa + 64 <= pe_v en \/ pe_v en + 56 <= fa).
{ rewrite Efa. destruct HVLOC as [(b & m & Hin & H1 & H2) | (cid & p' & Hin & H1 & H2)].
  - pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ b m 0 pos HAR Hin HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efb in Hd. clear - Hd H1 H2. lia.
  - destruct (in_split _ _ Hin) as (l2 & l3 & Hl).
    pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc _ W' mem mdc (0, pos) (cid, p') [] l2 l3 HAR
      ltac:(rewrite Hfrs, Hl; reflexivity)) as Hd.
    unfold frame_rng, zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efb in Hd. clear - Hd H1 H2. lia. }
assert (HDSH : SHADOW_OFF + fa / 8 + 8 <= pe_v en \/ pe_v en + 56 <= SHADOW_OFF + fa / 8).
{ destruct Hvlow as (_ & Hvapp). clear - Hvapp Hfapp CC1.
  unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (Hfalow : SHADOW_OFF + fa / 8 + 8 <= pe_sp en /\ fa + 64 <= pe_sp en).
{ clear - Hfac Hfa0 CC1 Hceil Hslo HSTK0. unfold SHADOW_OFF. lia. }
assert (Hvq : pe_v en + 56 <= pe_q en) by (clear - Hvlow Hceil Hslo HSTK0 Hqlo; lia).
(* ---- the callee's premises at the call state ---- *)
assert (HRO3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem)).
{ intros a Hr Ho Her. rewrite (J3 a (pvc_ro_img a Hr) Ho Her (RONP a Hr)).
  - exact (HRO a Hr Ho Her).
  - apply fp_spares_closed. apply sink_closed_pos. unfold pe_FP.
    apply Forall_cons; [cbn [fst]; clear - Hqlo Hsp64 Hceil Hslo HSTK0 CC1; lia|].
    apply Forall_cons; [cbn [fst]; clear - Hqlo Hsp64 Hceil Hslo HSTK0 CC1; lia|].
    apply Forall_cons; [cbn [fst]; clear - Hv4096; lia | apply Forall_nil]. }
assert (HQRA : range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF (pe_q en) 24).
{ apply (pvd_stack_ra B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc (pe_q en) 24 HAR).
  - rewrite Eloc. clear - Hslo HSTK0 Hqlo. lia.
  - rewrite Ehic. clear - Hqhi Hshij. lia. }
assert (HVAT : prhReader_at B lyc Sc (pe_Lam en) regs (pe_sp en + pe_e en - Y) (pe_v en) 4).
{ destruct Hvat as [(a0 & k0 & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
  - left. exists a0, k0. split; [exact Hin | clear - H1 H2; lia].
  - right; left. exists b, m. rewrite Habl. split; [exact Hin|]. split; [exact Hnl | clear - H1 H2; lia].
  - right; right; left. exists cid, p'. rewrite EFc. split; [exact (HinFr _ _ Hin) | clear - H1 H2; lia].
  - exfalso. unfold pe_sp in Hvwin. clear - H1 H2 Hvwin. destruct Hvwin; lia. }
assert (HVRA4 : range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF (pe_v en) 4)
  by (intros x Hx; apply HVRA; clear - Hx; lia).
assert (HTY : 0 <= pvd_lit_ty c <= 2)
  by (unfold pvd_lit_ty; destruct (c =? 116); [clear; lia | destruct (c =? 102); clear; lia]).
destruct (HCHAIN (aview SEGS (w_H W') mem) (fun a _ => eq_refl)) as (ch1 & Hch1).
assert (FP1n : forall a, ~ (pe_q en <= a < pe_q en + 8) -> ~ (pe_v en <= a < pe_v en + 4) ->
  ~ inFP [(pe_q en, pe_q en + 8); (pe_v en, pe_v en + 4)] a).
{ intros a H1 H2 (r & Hr & Hwr). destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hwr; [exact (H1 Hwr) | exact (H2 Hwr)]. }
assert (FPsub : forall a, ~ inFP (pe_FP en) a -> ~ inFP [(pe_q en, pe_q en + 8); (pe_v en, pe_v en + 4)] a).
{ intros a Hn (r & Hr & Hwr). apply Hn. destruct Hr as [<- | [<- | []]].
  - exists (pe_q en, pe_q en + 8). split; [unfold pe_FP; cbn [In]; left; reflexivity | exact Hwr].
  - exists (pe_v en, pe_v en + 56). split; [unfold pe_FP; cbn [In]; right; right; left; reflexivity|].
    cbn [fst snd] in Hwr |- *. clear - Hwr. lia. }
(* fpre's return-address bound at the call: the jal's return slot BASE + 0x86158 *)
assert (Hra3 : raZ regs < YM05.alloc_ceiling).
{ destruct (plookup (@pl_tpi _ PL_prog_B) AF_pv_lit_ret) as [e|] eqn:Hk; [|vm_compute in Hk; discriminate Hk].
  exact (pvd_ret_lt_ceil regs AF_pv_lit_ret e R1 ltac:(unfold AF_pv_lit_ret; lia) Hk). }
(* ---- THE CALL: literal(q, w, ty, v); its post is the m-form (fpostWm): the text's Q and the memnorm keep ---- *)
set (KL := fun (ly' : alayout) (S' : astate) (Hp' : list Z) (W2 : world SEGS) (regs' : bvmap 5 word)
    (mem' : word -> option byte) (md' : Model) =>
  ((room_live_cf Sc -> room_live_cf S') /\ Hp' = pe_Hp en /\ S' = Sc /\ ablocks B ly' S' = ablocks B lyc Sc /\
  prh_ledger B ly' S' Hp' W2 mem' (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en)
    (pe_own en) /\
  if PjGrammar.prefixb (pvd_lit_word c)
       (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y)))) then
    getr regs' 10 = w64 0 /\
    pj_in_okR SEGS (rdW W2 mem') (pe_q en) (pe_text en) (pe_len en)
      (pe_text en + pe_len en - Z.of_nat (length (c :: y)) + Z.of_nat (length (pvd_lit_word c)))
      (Z.of_nat (pe_d en)) (pe_tb en) /\
    val_mem SEGS (rdW W2 mem') (pe_v en) 4%nat (pvd_lit_ty c)
  else
    getr regs' 10 = w64 (-1) /\
    pj_in_okR SEGS (rdW W2 mem') (pe_q en) (pe_text en) (pe_len en)
      (pe_text en + pe_len en - Z.of_nat (length (c :: y))) (Z.of_nat (pe_d en)) (pe_tb en) /\
    (forall a, pe_q en <= a < pe_q en + 8 \/ pe_v en <= a < pe_v en + 4 ->
       aview SEGS (w_H W2) mem' a = aview SEGS (w_H W') mem a)) /\
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem')).
eapply SRr_bind.
{ apply (aj_call_xW SEGS B PSTX ARx LAWS (@pa_segs_low _ _ PA) W' regs mem (SIGMA AS_literal)
    (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en)
    (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) mdc k (STK_literal (PI := PIB)) (pe_sp en + pe_e en - Y)
    [(pe_q en, pe_q en + 8); (pe_v en, pe_v en + 4)] (Y - (pe_sp en + pe_e en))
    (Z_to_bv 64 (BASE + AF_pv_lit_ret)) ch1 KL HJ).
  - rewrite HspY. clear. lia.
  - clear - HY32 Hsp16 He16. lia.
  - clear - HYr He0. lia.
  - clear - HSL. lia.
  - clear - HSL HYr HSTKv. lia.
  - clear - HYr He0. lia.
  - clear - HY32 Hsp16 He16. lia.
  - clear. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [unfold AF_pv_lit_ret; clear; lia | reflexivity].
  - pose proof (@pa_B_ok _ B_prog_listing PA) as HBok.
    rewrite unsigned_lit_small; unfold AF_pv_lit_ret; clear - HBok; lia.
  - replace (pe_sp en + pe_e en + (Y - (pe_sp en + pe_e en))) with Y by (clear; lia).
    replace (s0Z regs) with (pe_sp en); [exact Hch1|]. unfold s0Z. rewrite R8. symmetry.
    apply unsigned_lit_small; clear - Hsp64; lia.
  - intros HAFN3 HWIN3.
    pose proof HAFN3 as (_ & _ & _ & _ & _ & Hstk3 & _).
    pose proof Hstk3 as (_ & _ & Hceil3 & Hslo3 & _).
    assert (HFP3 : fpre B ARx (STK_literal (PI := PIB)) lyc Sc (pe_Hp en) W' regs mem mdc ch1).
    { split; [exact HAFN3|]. split; [exact HRO3|]. split; [rewrite HspY, Ehic; clear - HYr Hshi; lia|].
      split; [exact Hra3 | exact Hfrm0]. }
    assert (HCSO : cstr_ok W' mem (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c))
      by exact (LITCS lyc Sc (pe_Hp en) W' mem mdc c HAR HRO3 Hc).
    destruct (pvc_slack W' mem _ _ HCSO) as (sl & Hgsl & Hlsl).
    pose proof HCSO as ((_ & Hnz) & _ & Hwceil & _).
    pose proof (Z.mod_pos_bound (- (VAL (A_OBJ 2) + pvd_word_off c + Z.of_nat (length (pvd_lit_word c)) + 1)) 8
      ltac:(clear; lia)) as Hsl8.
    assert (HNZ : ~ In 0 (pvd_lit_word c)).
    { intros Hin. rewrite Forall_forall in Hnz. exact (Hnz 0 Hin eq_refl). }
    assert (HBND : VAL (A_OBJ 2) + pvd_word_off c + Z.of_nat (length (pvd_lit_word c)) + 1 + Z.of_nat (length sl)
      <= 2 ^ 63) by (clear - Hwceil Hsl8 Hlsl CC1; lia).
    assert (HALN : (- (VAL (A_OBJ 2) + pvd_word_off c + Z.of_nat (length (pvd_lit_word c)) + 1)) mod 8
      <= Z.of_nat (length sl)) by (rewrite Hlsl; apply Z.le_refl).
    (* the word's NUL-aligned end s + (- s) mod 8 (s = w + |cw| + 1) is below the stack: cstr_ok bounds s itself by
       alloc_ceiling (SRC-CEIL, no `+ 8`), which is 4096-aligned (YM05.alloc_ceiling_value), so the next multiple of
       8 from s is at most alloc_ceiling <= the callee's stack low end (astk_ok) *)
    assert (HBELOW : spZ regs <= VAL (A_OBJ 2) + pvd_word_off c \/
      VAL (A_OBJ 2) + pvd_word_off c + Z.of_nat (length (pvd_lit_word c)) + 1 + Z.of_nat (length sl)
      <= spZ regs - STK_literal (PI := PIB)).
    { right. pose proof (proj2 YM05.alloc_ceiling_value) as HCm.
      pose proof (Z_div_mod_eq_full YM05.alloc_ceiling 4096) as HCd.
      pose proof (Z_div_mod_eq_full (- (VAL (A_OBJ 2) + pvd_word_off c + Z.of_nat (length (pvd_lit_word c)) + 1)) 8)
        as HSd.
      clear - Hwceil Hsl8 Hlsl Hceil3 Hslo3 HCm HCd HSd. lia. }
    assert (HqY : spZ regs <= pe_q en) by (rewrite HspY; clear - HYr Hqlo; lia).
    assert (Hqt3 : pe_q en + 24 <= spZ regs + (pe_sp en + pe_e en - Y)) by (rewrite HspY; clear - Hqhi; lia).
    exact (TLIT lyc Sc (pe_Hp en) W' regs mem mdc ch1 (pe_sp en + pe_e en - Y) (pe_q en) (pe_text en) (pe_len en)
      (pe_text en + pe_len en - Z.of_nat (length (c :: y))) (Z.of_nat (pe_d en)) (pe_tb en)
      (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c) sl (pvd_lit_ty c) (pe_v en) (pe_Lam en) (pe_peak en)
      (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) HFP3 R10 R11 R12 R13 HCUR HWIN3 HqY Hqt3 HQRA
      HSRC HHOME HCSO HBND Hgsl
      HNZ HALN HBELOW HTY ltac:(clear - Hv4096; lia) Hv8 HVAT HVRA4 ltac:(clear - Hqv; lia)
      ltac:(clear - Htv; lia) HLEDc).
  - intros a Ha. left. destruct Ha as (r & Hr & Hwr). destruct Hr as [<- | [<- | []]].
    + exists (pe_q en, pe_q en + 8). split; [unfold pe_FP; cbn [In]; left; reflexivity | exact Hwr].
    + exists (pe_v en, pe_v en + 56). split; [unfold pe_FP; cbn [In]; right; right; left; reflexivity|].
      cbn [fst snd] in Hwr |- *. clear - Hwr. lia. }
cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & Ec4 & HJ4 & HJc & HXw & HP4 & HKL).
subst c4. unfold KL in HKL. destruct HKL as ((Hroom4 & EHp4 & ES4 & Eab4 & HLED4 & Hpost) & HMK4). subst Hp4.
assert (HMN4 : YAkMemnorm.memnorm SEGS mem4) by exact (HMK4 HMNc).
pose proof HJ4 as (HAR4 & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & M2 & _ & M4 & _ & Hpresc & _).
cbn [app] in Hfrsc.
pose proof Hlyc as (_ & _ & _ & _ & _ & EF4' & _).
assert (EF4 : forall c0 p0, frame_addr ly4 c0 p0 = frame_addr lyc c0 p0)
  by (intros; unfold frame_addr; rewrite EF4'; reflexivity).
assert (EFl4 : forall c0 p0, flag_addr ly4 c0 p0 = flag_addr lyc c0 p0)
  by (intros; unfold flag_addr; rewrite EF4'; reflexivity).
assert (HinF4 : In (0, pos) (frames S4)) by (rewrite Hfrsc; exact HinF).
(* ---- what literal kept ---- *)
assert (HFRM4 : pv_frame (pe_regs en) (pe_sp en) Y fa fl pv_shadow_live W4 mem4).
{ apply (pvc_frame_trW _ _ _ _ _ _ W' W4 mem mem4); [| | exact HFRM].
  - intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    + apply HXw; [clear - Ha He0; lia | apply FP1n; clear - Ha Hqlo Hvlow Hceil Hslo HSTK0 HSTKv HYr; lia].
    + apply (M4 0 pos a HinF).
      * left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- Efa, Efb. clear - Ha. lia.
      * apply FP1n; clear - Ha Hfalow Hqlo HDFA; lia.
    + apply (M4 0 pos a HinF).
      * right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- Efa, Efb. clear - Ha. lia.
      * apply FP1n; clear - Ha Hfalow Hqlo HDSH; lia.
  - intros a Ha. destruct Ha as [Ha | Ha].
    + apply Hpresc. clear - Ha HSL He0 HYr. lia.
    + destruct (alx_frames SEGS B ARx LAWS ly4 S4 (pe_Hp en) W4 mem4 md4 0 pos HAR4 HinF4) as (_ & _ & Hfb4 & _).
      rewrite EF4, <- Efa, Efb in Hfb4. exact (proj1 (Hfb4 a Ha)). }
assert (Hkeep4 : forall a, pe_v en + 4 <= a < pe_v en + 56 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W') mem a).
{ intros a Ha.
  assert (Hn : ~ inFP [(pe_q en, pe_q en + 8); (pe_v en, pe_v en + 4)] a) by (apply FP1n; clear - Ha Hvq; lia).
  destruct HVLOC as [(b & m & Hin & H1 & H2) | (cid & p' & Hin & H1 & H2)].
  - replace a with (b + (a - b)) by (clear; lia).
    apply (M2 b m (a - b) Hin); [rewrite Eab4; exact Hin | clear - Ha H1 H2; lia |].
    replace (b + (a - b)) with a by (clear; lia). exact Hn.
  - apply (M4 cid p' a (HinFr _ _ Hin)); [left; unfold frame_rng, in_zr; cbn [fst snd]; clear - Ha H1 H2; lia | exact Hn]. }
assert (R10c : getr regs4 10 = w64 (if PjGrammar.prefixb (pvd_lit_word c)
    (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y)))) then 0 else -1)).
{ revert Hpost. destruct (PjGrammar.prefixb (pvd_lit_word c)
    (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y)))));
    intros Hpost; exact (proj1 Hpost). }
assert (HQ4 : if PjGrammar.prefixb (pvd_lit_word c)
        (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y))))
   then
     pj_in_okR SEGS (rdW W4 mem4) (pe_q en) (pe_text en) (pe_len en)
       (pe_text en + pe_len en - Z.of_nat (length (c :: y)) + Z.of_nat (length (pvd_lit_word c)))
       (Z.of_nat (pe_d en)) (pe_tb en) /\
     val_mem SEGS (rdW W4 mem4) (pe_v en) 4 (pvd_lit_ty c)
   else
     pj_in_okR SEGS (rdW W4 mem4) (pe_q en) (pe_text en) (pe_len en)
       (pe_text en + pe_len en - Z.of_nat (length (c :: y))) (Z.of_nat (pe_d en)) (pe_tb en) /\
     (forall a, pe_v en <= a < pe_v en + 4 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W') mem a)).
{ revert Hpost. destruct (PjGrammar.prefixb (pvd_lit_word c)
    (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y)))));
    intros (_ & Hin' & Hv'); (split; [exact Hin'|]).
  - exact Hv'.
  - intros a Ha. apply Hv'. right. exact Ha. }
assert (Q2 : getr regs4 2 = getr regs 2) by pvc_keep HP4 (2%bv : bv 5) 2.
assert (Q3 : getr regs4 3 = getr regs 3) by pvc_keep HP4 (3%bv : bv 5) 3.
assert (Q4 : getr regs4 4 = getr regs 4) by pvc_keep HP4 (4%bv : bv 5) 4.
assert (Q8 : getr regs4 8 = getr regs 8) by pvc_keep HP4 (8%bv : bv 5) 8.
assert (Q18 : getr regs4 18 = getr regs 18) by pvc_keep HP4 (18%bv : bv 5) 18.
assert (Q23 : getr regs4 23 = getr regs 23) by pvc_keep HP4 (23%bv : bv 5) 23.
assert (Q26 : getr regs4 26 = getr regs 26) by pvc_keep HP4 (26%bv : bv 5) 26.
assert (Q27 : getr regs4 27 = getr regs 27) by pvc_keep HP4 (27%bv : bv 5) 27.
(* ---- B 0x86648: `mv s5, a0`, to the exit 0x8664c, from a fresh symbolic state ---- *)
set (E := Eimg (Ereg regs4 [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs4 []) E).
{ unfold E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; clear - Hn; lia | reflexivity]. }
assert (HS : st_ok_pi SEGS VAL E pvc_ss
  (restrict (w_H W4) (@YK11.mkst fx0 regs4 (Z_to_bv 64 (BASE + AF_pv_lit_ret)) mem4 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pvc_ss.
  replace (Z_to_bv 64 (BASE + AF_pv_lit_ret)) with (Z_to_bv 64 (VAL A_TEXT + AF_pv_lit_ret)) by reflexivity.
  apply pa_entry_st_ok_full.
  - unfold E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS PVC_Bx [] E (rdW W4 mem4)) by apply Forall_nil.
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS)).
paj_run_to_tok_x_inv RUNTO HS HJ4 SHOK HMN4 PVC_Bspan AF_pv_exit.
{ intros a (r & Hin & _). unfold pvc_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin. }
rewrite ?wvb_collapse in HJ4.
lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
assert (EQ : forall x, rdW W4 (ms_mem msf) x = rdW W4 mem4 x).
{ apply (pvd_nowin E (ss_mem pvc_ss)); [|exact HFr]. intros a (r & Hin & _). unfold pvc_ss in Hin.
  cbn [ss_mem In] in Hin. destruct Hin. }
assert (GR : forall a, apresent (w_H W4) mem4 a -> apresent (w_H W4) (ms_mem msf) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a HG), Ha).
assert (AVF : forall a, aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a)
  by (intros a; apply aview_eq_of; apply EQ).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HAEf : env_agree 32 (Ereg regs4 []) Ex) by (pvd_agree HAE) end.
assert (KR : forall r, In r [2; 3; 4; 8; 18; 23; 26; 27]%bv -> getr (ms_regs msf) r = getr regs4 r)
  by (intros r Hr; exact (regs_kept_of_st_ok_pi _ _ _ regs4 [] [2; 3; 4; 8; 18; 23; 26; 27]%bv HS HAEf
        ltac:(vm_compute; reflexivity) r Hr)).
pvd_reg HS (21%bv : bv 5) R21.
assert (R21' : getr (ms_regs msf) 21 = getr regs4 10).
{ rewrite R21. cbn [sv_denot]. rewrite (proj1 HAEf 10%nat ltac:(pvd_nat)), Z.add_0_r.
  change (ew (Ereg regs4 []) 10) with (getr regs4 10). apply Z_to_bv_bv_unsigned. }
pmkst HS. apply HKX.
exists fx0, (ms_regs msf), (ms_mem msf), Y, fa, fl, pos, ly4, S4, (pe_Hp en), (k + k1),
  (if PjGrammar.prefixb (pvd_lit_word c)
        (rest_atR (pe_tb en) (pe_text en) (pe_text en + pe_len en - Z.of_nat (length (c :: y)))) then 0 else -1).
split; [first [reflexivity | repeat f_equal; try (vm_compute; reflexivity)]|].
split; [exact Hfrm0|]. split; [intros r _; reflexivity|].
split.
{ unfold pv_keep_regs. rewrite !KR by (cbn; tauto). rewrite Q2, Q8, Q18, Q26, Q27, Q23, Q3, Q4.
  split; [exact R2|]. split; [exact R8|]. split; [exact R18|]. split; [exact R26|]. split; [exact R27|].
  split; [exact R23|]. split; [exact R3 | exact R4]. }
split; [rewrite R21'; exact R10c|].
split.
{ apply pv_body_x_of.
  split; [|split; [exact HinF4|split; [rewrite EF4; exact Efa|split; [rewrite EFl4; exact Efl|split; [exact HJ4|]]]]].
  - apply (pvd_frame_tr _ _ _ _ _ _ W4 mem4); [intros a _; apply pvd_mbyte_eq, EQ | intros a _; apply GR | exact HFRM4].
  - intros a Ha Hn. rewrite AVF.
    rewrite HXw; [exact (HWIN a Ha Hn) | clear - Ha HYr; lia | apply FPsub; exact Hn]. }
(* the post's memory part, its room post by the keep from entry (literal keeps the state: S' = S), and the memory
   normal form at the exit *)
assert (HPOS4 : rp_keep (pe_S en) S4) by (rewrite ES4; exact HRPc).
assert (HSEC4 : YGcfSecsStep.secs_same (pe_S en) S4) by (rewrite ES4; exact HSECc).
split; [exact (pvc_Qm en c y pos lyc Sc W' mem ly4 S4 W4 mem4 (ms_mem msf) HPRE Hsk Hc HRD0 EQ Hroom4 Eab4 Hfrsc HLED4
  HPOS4 HSEC4 HQ4 Hkeep4)|].
exact HMN4.
Qed.

End c.
