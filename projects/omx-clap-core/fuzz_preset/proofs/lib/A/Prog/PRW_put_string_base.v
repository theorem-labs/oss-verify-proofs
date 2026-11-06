(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ex_ws_x.v, with its module paths and module names changed; 1951 of its 2020 lines of code are new or changed and 807 lines of the source are left out. *)
(* fuzz_preset image A, slice S7b (WalkS7b.S7bPutString): the program walk of put_string (A 0x8836c, 221 instructions)
   over the ONE image-A program listing (lib/A/Listing_prog.v, a Theorem Labs lane), generic in the image facts (Context PAImg)
   and in the allocator relation ARx (LAWS : AR_laws_x), concluding the kit's text tput_string_specX
   (lib/A/PRH_FnWriter.v) in srealizes / SRr form.
   KIT: the kit's cut 7cdbb61b5fa0 (re-fitted on the batch kit's tip 44123abafeb7, merged forward unchanged: PRH_FnWriter.v d89d3c67b78c, PRH_Base.v
   ef7c8ca98529; S7a_WriterRet.v 8c237bd1fbb4): the ledger carries `most own`; fpre's last conjunct is frm_zero
   (FRM0-ENTRY); the text takes its consumer window prh_cons_from and its per-event live room prh_live_evs at entry
   (put's are supplied by S7a_WriterRet's prhWriter_cons_at / prhWriter_live_evs_at in ps_put_step), and posts the
   FLOAT form fpostWFm with prh_granted (DEAD-PUTSTRING). THE FLOAT THREADING (WalkS7bR's internal file REFIT-WRITER.md): the
   record holds the ENTRY float state x_fx;
   the pre is stated at it (fpre (fx := x_fx X)), the final post ps_Qfin is the float form relative to it, and every
   join carries the CURRENT float state's relation (frm_zero of the current fx, fregs_kept_x (x_fx X) fx); the joins
   are this file's definitions, so after this file they are generic in fx (a segment states a continuation at fx').
   Engine: YC80x / YC1fPx (paj_run_x, paj_run_tok_x) over YCbqG's ajournal_x; stretches with stores into the fake
   frame's shadow run on this file's tokenless port of cgif YC44.v (SRr_run_to_pi_AJx).
   Rule 24: not in released set (proof-index put_string, 2026-10-28T23:37Z: released hits are the plain / UBSan
   images' put_string, control-flow references only).
   structural reference only: a working branch e09c6006f5b lib/A/Prog/put_string.v, put_string_esc.v,
   put_string_open.v (ORIGINAL image, old framework; read for control flow, nothing cited or copied).
   Numerals: 208 (LENGTH: put_string's frame, the kit's pi_frame); offsets inside the function (116, 276, 384, 672: slot
   deltas times 4, from Listing_prog). No address literal: put_string's entry and the literals are by name (A_prog_slot,
   the listing's PAddHi addends). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the step relation over a world relation and the re-hiding relation (SRrG, wle', SRr') and the fixed zone RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* the call rule over a world relation (aj_call_xWR), by its qualified name: PRW_CallerJ's copies keep the plain names *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_S7bKit PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia must see the division equations: the realignment is a mod 32 (never rely on an inherited flag) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's generated numbers (PRH_Img.v) are the PrhImg the texts read *)
#[local] Existing Instance prh_img_A.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
(* The kit's non-primary room invariant (PRH_Base.v PrhRoomLive, owner a Theorem Labs lane) *)
Context {RL : PrhRoomLive}.
(* ---- The kit's run events of a run of puts (PRH_FnWriter.v d89d3c67b78c at the cut: prhWriter_evs): the count after one more put.
   The count is a function of the start and end states (S7a's prhW_evs_len, S7a_WriterRet.v 29e79f90789a), and a run
   only appends calls, so a run P1 followed by one put b (S7a's prhW_app_model gives the composed run's end state)
   makes P1's events plus ONE exactly when that put grew and left the writer not failed - the arm tput_specX's
   per-arm post advances the position on. ---- *)
Lemma ps_calls_prefix : forall P ok st,
  exists l, WriterApp.w_calls (prhWriter_putN ok st P) = WriterApp.w_calls st ++ l.
Proof.
induction P as [|b P IH]; intros ok st; [exists []; rewrite app_nil_r; reflexivity|].
destruct (prhWriter_grows st b) eqn:Hg.
- rewrite (prhW_putN_cons_grow ok st b P Hg).
  destruct (IH (tl ok) (prhWriter_put1 (hd true ok) st b)) as (l & El).
  rewrite El, (prhW_put1_grow_calls (hd true ok) st b Hg), <- app_assoc. eexists; reflexivity.
- rewrite (prhW_putN_cons_nogrow ok st b P Hg).
  destruct (IH ok (WriterApp.put1 st b)) as (l & El).
  destruct (prhW_nogrow_f st b Hg) as (_ & _ & _ & _ & Ec). rewrite El, Ec. eexists; reflexivity.
Qed.

Lemma ps_len_one : forall st P1 b okJ ok1 ok2,
  prhWriter_putN okJ st (P1 ++ [b]) = prhWriter_putN ok2 (prhWriter_putN ok1 st P1) [b] ->
  length (prhWriter_evs okJ st (P1 ++ [b])) =
    (length (prhWriter_evs ok1 st P1) +
     (if prhWriter_grows (prhWriter_putN ok1 st P1) b &&
         (WriterApp.w_failed (prhWriter_putN ok2 (prhWriter_putN ok1 st P1) [b]) =? 0)%Z then 1 else 0))%nat.
Proof.
intros st P1 b okJ ok1 ok2 Hput.
pose proof (prhW_evs_len (P1 ++ [b]) okJ st) as LJ. pose proof (prhW_evs_len P1 ok1 st) as L1.
unfold prhWriter_k in LJ, L1. rewrite Hput in LJ.
destruct (ps_calls_prefix P1 ok1 st) as (l1 & El1).
set (st1 := prhWriter_putN ok1 st P1) in *.
destruct (prhWriter_grows st1 b) eqn:Hg.
- assert (Hf1 : WriterApp.w_failed st1 = 0)
    by (unfold prhWriter_grows in Hg; apply andb_prop in Hg as (Hg' & _); apply Z.eqb_eq in Hg'; exact Hg').
  assert (Hf0 : WriterApp.w_failed st = 0).
  { destruct (Z.eq_dec (WriterApp.w_failed st) 0) as [E | E]; [exact E | exfalso].
    pose proof (prhW_putN_failed P1 ok1 st E) as Est. fold st1 in Est. rewrite Est in Hf1. exact (E Hf1). }
  assert (E2 : prhWriter_putN ok2 st1 [b] = prhWriter_put1 (hd true ok2) st1 b)
    by (rewrite (prhW_putN_cons_grow ok2 st1 b [] Hg); reflexivity).
  rewrite E2 in LJ |- *. rewrite (prhW_put1_grow_calls (hd true ok2) st1 b Hg), El1, !length_app in LJ.
  rewrite El1, length_app in L1. cbn [length] in LJ.
  rewrite Hf0, Hf1 in L1. rewrite Hf0 in LJ. cbn [Z.eqb andb negb] in L1, LJ.
  revert LJ. destruct (Z.eqb_spec (WriterApp.w_failed (prhWriter_put1 (hd true ok2) st1 b)) 0) as [Hz | Hnz];
    intros LJ; cbn [negb andb] in LJ |- *; lia.
- assert (E2 : prhWriter_putN ok2 st1 [b] = WriterApp.put1 st1 b)
    by (rewrite (prhW_putN_cons_nogrow ok2 st1 b [] Hg); reflexivity).
  rewrite E2 in LJ. destruct (prhW_nogrow_f st1 b Hg) as (Ef & _ & _ & _ & Ec).
  rewrite Ef, Ec in LJ. cbn [andb]. lia.
Qed.

Section f.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

(* put_string's offset in the listing (DERIVED: slot 7011 * 4) *)
Definition AF_put_string : Z := 4 * Z.of_nat (A_prog_slot AS_put_string).
Definition PS_SB : Z := SHADOW_OFF.
Definition PS_Bx : sv := SOff 32 0.
Definition PS_Bspan : Z * Z := (PS_SB, PS_SB + 2 ^ 44 - 1).
(* the GOT word of the use-after-return flag (A_OBJ 1) holds the flag's address (atom 33); the flag holds 1 *)
Definition uargot_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition uarcell_region : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
(* the realigned stack pointer (sp - 192) & -32 is atom 34; the alias lets the engine name it *)
Definition PS_AND : sv := SAlu ALU_AND (SOff 2 (-192)) (SLit (-32)).
(* the saved registers' slots (sp - 104 .. sp) and the realigned frame's slots (R .. R + 88) *)
Definition saved_region : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition rframe_region : YP09.region := YP09.mkRegion (Some 34%nat) 0 88 0 88 [].
Definition ps_regions2 : smem :=
  [ saved_region; rframe_region; got_regionP; bcell_regionP 32; uargot_region; uarcell_region ].
Definition ps_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47) 3);
            (11%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF PS_SB PS_SB 0); (33%nat, mkAF 0 (2 ^ 31) 0);
            (34%nat, mkAF (2 ^ 46 - 208) (2 ^ 47) 5) ] [] [(PS_AND, SOff 34 0)].
Definition ps_ss2 : sstate := mkSS (AF_put_string + 8) (sr_set sr_atoms 2%bv (SOff 2 (-192))) ps_regions2 None ps_facts.
Definition ps_SH : list shent := [].

(* ---- small state facts (own lemmas) ---- *)
Lemma val_mem_of_rd32 : forall H (mem : word -> option byte) a v,
  rd32 (aview SEGS H mem) a v -> val_mem SEGS (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. destruct (aview_byte SEGS H mem _ _ (Hr k Hk)) as (b & Hb & Hv & _).
rewrite Hb. f_equal. unfold YG0f.le_byte in Hv. unfold YO0f.le_byte. rewrite Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* PORT of cgif YC1h.v:107-110 *)
Lemma st_ok_pi_submem : forall E ss ms rs,
  st_ok_pi SEGS VAL E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof. intros E ss ms rs HS Hs Hwf. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. exact (st_ok_submem SEGS E _ ms rs HS Hs Hwf). Qed.
(* PORT of cgif YC44.v:395-398 *)
Lemma st_ok_pi_add_alias : forall E ss ms e1 e2,
  st_ok_pi SEGS VAL E ss ms -> sv_denot E e1 = sv_denot E e2 ->
  st_ok_pi SEGS VAL E (set_facts ss (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((e1, e2) :: f_alias (ss_facts ss)))) ms.
Proof. intros E ss ms e1 e2 HS He. destruct ss as [p0 r0 f0 m0 v0 g0]. exact (st_ok_add_alias SEGS E _ ms e1 e2 HS He). Qed.
(* PORT of cgif YC1h.v:44-51: fresh atoms above every atom of the state *)
Lemma st_ok_pi_havoc_hi : forall k E ss ms ws,
  st_ok_pi SEGS VAL E ss ms -> ss_atoms_p (pband k (k + length ws)) ss = true ->
  st_ok_pi SEGS VAL (havoc E k ws) ss ms.
Proof.
intros k E ss ms ws HS Hat. unfold st_ok_pi in *.
eapply (st_ok_agree_p (pband k (k + length ws)) SEGS); [exact HS | | destruct ss; exact Hat].
apply env_agree_p_havoc. apply le_n.
Qed.
(* the fake frame (atom f; its flag cell's address at f + 56 is atom fl), its shadow bytes (atom sh), the realigned
   frame's slots *)
Definition fframe_reg (f fl : nat) : YP09.region :=
  YP09.mkRegion (Some f) 0 64 0 32 [YP09.mkChunk 56 (CVal 8 (SOff fl 0))].
Definition fshadow_reg (sh : nat) : YP09.region := YP09.mkRegion (Some sh) 0 8 0 8 [].
(* PORT of YCem.v rdword_of_val_mem (its file does not build in this unit): a word's bytes read back as the word *)
Lemma rdword_of_vm : forall H mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
  apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hr.
Qed.
Lemma rdword_range_ps : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
destruct (aview_byte SEGS _ _ _ _ E0) as (_ & _ & _ & R0). destruct (aview_byte SEGS _ _ _ _ E1) as (_ & _ & _ & R1).
destruct (aview_byte SEGS _ _ _ _ E2) as (_ & _ & _ & R2). destruct (aview_byte SEGS _ _ _ _ E3) as (_ & _ & _ & R3).
destruct (aview_byte SEGS _ _ _ _ E4) as (_ & _ & _ & R4). destruct (aview_byte SEGS _ _ _ _ E5) as (_ & _ & _ & R5).
destruct (aview_byte SEGS _ _ _ _ E6) as (_ & _ & _ & R6). destruct (aview_byte SEGS _ _ _ _ E7) as (_ & _ & _ & R7).
lia.
Qed.

(* ---- PORT of cgif YC44.v:407-452 (origin/ossv/recipes): the listing engine WITHOUT shadow tokens, over YCbqG's
   ajournal_x (journal step YCbqG.v SRr_chain_AJx). put_string's stores into its fake frame's shadow (the poisoning
   at A 0x88448-0x88468, 0x884ec, 0x885bc, 0x88644-0x88660) lie in the shadow span the token engine reserves, so those
   stretches run here; a stretch may end at a call (the post at the callee's entry, as YC80x's runner). ---- *)
Section nt.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx).
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R).
Definition run_post_pi_AJx (W : world SEGS) (E : env) (ss ss' : sstate) (st : prun_status asym)
  (ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall ms' mat',
  match st with
  | PRS_call s => st_ok SEGS E (setpc ss' (SIGMA s)) (restrict (w_H W) ms')
  | _ => st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms')
  end ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* run_post_pi_AJx over a world relation R: the journal at R (YCbqG.v ajournal_xR) and the conclusion SRrG SEGS R.
   A run after a free or a realloc of a live block states its journal at the re-hiding relation (YA0nH.v wle'); its
   instance at wle is run_post_pi_AJx (run_post_pi_AJx_R_wle). *)
Definition run_post_pi_AJxR (R : world SEGS -> world SEGS -> Prop) (W : world SEGS) (E : env) (ss ss' : sstate)
  (st : prun_status asym) (ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc
  (mdc : Model) (k : Z) (Q : world SEGS -> config -> Prop) : Prop :=
  forall ms' mat',
  match st with
  | PRS_call s => st_ok SEGS E (setpc ss' (SIGMA s)) (restrict (w_H W) ms')
  | _ => st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms')
  end ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRrG SEGS R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma run_post_pi_AJx_R_wle : forall W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  run_post_pi_AJx W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q =
  run_post_pi_AJxR (@wle SEGS) W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q.
Proof. reflexivity. Qed.
Lemma SRr_run_to_pi_AJx : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) n stop ss = (ss', st) ->
  match st with PRS_ecall => False | _ => True end ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_pi_AJx W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- (@pl_tpi_eq A_prog_listing PL_prog_A) in Hrun.
destruct (YP0d.sym_run_to_pi_sound asym SEGS (clookup pa_tbl) VAL pa_sigma A_prog_listing pa_fetch_ok pa_cert pa_B_ok
  A_LIM A_LIM_text (@pl_lim A_prog_listing PL_prog_A) _ _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
destruct st as [| | s |why]; cbn [prun_post] in HP; [| destruct Hst | |].
- eapply (SRr_chain_AJx (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
- eapply (SRr_chain_AJx (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (setpc ss' (SIGMA s)) ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
- eapply (SRr_chain_AJx (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
End nt.
(* the P-twin of the tokenless runner (YSRrMemnorm.v's form: SRr_msteps_inv in place of SRr_msteps): a memory
   invariant P with its laws is carried across the run *)
Section ntp.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx).
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R).
Definition run_post_pi_AJx_inv (W : world SEGS) (E : env) (ss ss' : sstate) (st : prun_status asym)
  (ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
  (Q : world SEGS -> config -> Prop) : Prop :=
  forall ms' mat',
  match st with
  | PRS_call s => st_ok SEGS E (setpc ss' (SIGMA s)) (restrict (w_H W) ms')
  | _ => st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms')
  end ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* run_post_pi_AJx_inv over a world relation R: the journal at R and the conclusion SRrG SEGS R; its instance at wle
   is run_post_pi_AJx_inv (run_post_pi_AJx_inv_R_wle) *)
Definition run_post_pi_AJx_invR (R : world SEGS -> world SEGS -> Prop) (W : world SEGS) (E : env) (ss ss' : sstate)
  (st : prun_status asym) (ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc
  (mdc : Model) (k : Z) (Q : world SEGS -> config -> Prop) : Prop :=
  forall ms' mat',
  match st with
  | PRS_call s => st_ok SEGS E (setpc ss' (SIGMA s)) (restrict (w_H W) ms')
  | _ => st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms')
  end ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRrG SEGS R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma run_post_pi_AJx_inv_R_wle : forall W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  run_post_pi_AJx_inv W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q =
  run_post_pi_AJx_invR (@wle SEGS) W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q.
Proof. reflexivity. Qed.
(* SRr_chain_AJx_inv below over a world relation R (reflexive, transitive): the run step SRr_msteps_invR, the
   journal step ajournal_x_execR *)
Lemma SRr_chain_AJx_invR : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  msteps SEGS (restrict (w_H W) ms) msr' ->
  st_ok SEGS E ss' msr' ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat', st_ok SEGS E ss' (restrict (w_H W) ms') ->
     AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     P (ms_mem ms') ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRrG SEGS R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms HS' Hfr HJ HPm Hwr Hk.
apply (SRr_msteps_invR SEGS pa_wx P PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows SEGS _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- eapply (ajournal_x_execR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS pa_segs_low R)
    with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
  + rewrite Hmm. exact Hfr.
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* YCbqG.v SRr_chain_AJx with SRr_msteps_inv: the R form at wle *)
Lemma SRr_chain_AJx_inv : forall W E ss ss' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  msteps SEGS (restrict (w_H W) ms) msr' ->
  st_ok SEGS E ss' msr' ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat', st_ok SEGS E ss' (restrict (w_H W) ms') ->
     AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     P (ms_mem ms') ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_AJx_invR (@wle SEGS) (wle_refl SEGS) (wle_trans SEGS)). Qed.
(* SRr_run_to_pi_AJx_inv below over a world relation R (reflexive, transitive) *)
Lemma SRr_run_to_pi_AJx_invR : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) n stop ss = (ss', st) ->
  match st with PRS_ecall => False | _ => True end ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_pi_AJx_invR R W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ HPm Hwr Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- (@pl_tpi_eq A_prog_listing PL_prog_A) in Hrun.
destruct (YP0d.sym_run_to_pi_sound asym SEGS (clookup pa_tbl) VAL pa_sigma A_prog_listing pa_fetch_ok pa_cert pa_B_ok
  A_LIM A_LIM_text (@pl_lim A_prog_listing PL_prog_A) _ _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
destruct st as [| | s |why]; cbn [prun_post] in HP; [| destruct Hst | |].
- eapply (SRr_chain_AJx_invR R Rr Rt W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | exact HPm | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HP' HF HF' HG. apply (Hk ms' mat' HS' HJ' HP'); destruct ss; first [exact HF | exact HF' | exact HG].
- eapply (SRr_chain_AJx_invR R Rr Rt W E (abs_ss VAL ss) (setpc ss' (SIGMA s)) ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | exact HPm | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HP' HF HF' HG. apply (Hk ms' mat' HS' HJ' HP'); destruct ss; first [exact HF | exact HF' | exact HG].
- eapply (SRr_chain_AJx_invR R Rr Rt W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
  [ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | exact HPm | destruct ss; exact Hwr | ].
  intros ms' mat' HS' HJ' HP' HF HF' HG. apply (Hk ms' mat' HS' HJ' HP'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
Lemma SRr_run_to_pi_AJx_inv : forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) n stop ss = (ss', st) ->
  match st with PRS_ecall => False | _ => True end ->
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  P (ms_mem ms) ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_pi_AJx_inv W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_AJx_invR (@wle SEGS) (wle_refl SEGS) (wle_trans SEGS)). Qed.
End ntp.
(* SRr_run_to_pi_AJx over a world relation R: the P-twin at the trivial P *)
Section ntr.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R).
Lemma SRr_run_to_pi_AJxR : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) n stop ss = (ss', st) ->
  match st with PRS_ecall => False | _ => True end ->
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  run_post_pi_AJxR B ARx R W E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E ss ss' st ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
apply (SRr_run_to_pi_AJx_invR B ARx LAWS (fun _ => True) (srr_inv_laws_true SEGS) R Rr Rt W n stop E ss ss' st ms
  STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HE HS Hrun Hst HJ I Hwr).
intros ms' mat' H1 H2 _ H4 H5 H6. exact (Hk ms' mat' H1 H2 H4 H5 H6).
Qed.
End ntr.


(* the probe word `sd zero, 0(sp)` writes at sp - 192 before the realignment *)
Definition probe_region : YP09.region := YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [].
Definition ps_ss0 : sstate :=
  mkSS AF_put_string sr_atoms [ probe_region; saved_region; got_regionP; bcell_regionP 32; uargot_region; uarcell_region ]
    None ps_facts.
(* the realigned stack pointer (sp - 192) & -32 *)
Definition PS_R (sp : Z) : Z := sp - 192 - (sp - 192) mod 32.
Definition ps_E (regs : bvmap 5 word) (uar : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 PS_SB; Z_to_bv 64 uar; Z_to_bv 64 (PS_R (spZ regs))]).

(* land_m32 (the `andi sp, sp, -32` realignment) is PRW_StepKit.land_m32, the one copy *)

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
(* the entry (DERIVED: slot * 4, PAImg_prog A_entry_put_string) *)
Hypothesis Hent : SIGMA AS_put_string = BASE + AF_put_string.
(* image-link gap, proposed PALib field pal_got_uar *)
Hypothesis Huar : as_got_uar B = VAL (A_OBJ 1).
(* image facts, discharged at PI_prog_A: the GOT words of the shadow base and of the use-after-return flag, the shadow
   cell and the flag cell lie in the image's segments and apart *)
Hypothesis Hobj : forall i, 0 <= i < 8 ->
  in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i) /\ in_img SEGS (VAL (A_OBJ 1) + i).
Definition ps_objs_disj : Prop := (VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 1)) /\
  (VAL (A_OBJ 1) + 8 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 1)).
Definition ps_uar_ok : Prop := (forall i, 0 <= i < 4 -> in_img SEGS (as_uar_cell B + i)) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell B).
Hypothesis HOBJ : ps_objs_disj.
Hypothesis HUARC : ps_uar_ok.
(* the engine's / instance's side conditions of the frame-area step (YGcallSx.v Section x, owner c-omx-alloc) *)
Hypothesis segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env SEGS B.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).
(* frame class 0's text in the m-form (YGcallMxmn astack_malloc_realizes_xm, owner R4) and its entry; image-link gap *)
Hypothesis ASM0 : astack_malloc_realizes_xm SEGS B ARx 0.
Hypothesis Hsm0 : pc_stack_malloc (as_code B) 0 = SIGMA AS___asan_stack_malloc_0.
(* the head is at least one shadow granule wide (PRH_Base.v's one spelling, discharged by a8's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* the registered zero-shadow ranges are granule-aligned (YG0f.v asyms_ok's aso_zshadow; image fact of the instance,
   discharged at PI_prog_A) *)
Hypothesis ASO : asyms_ok B.
(* the image's shadow is visible (PRW_HShadow.v ARx_img_shadow_vis, owner a8 YImgShadowCoverCf.v) and every live fake
   frame's shadow hull (ARx_frame_hull_vis, owner a8 YGcfFsVis.v) *)
Hypothesis HIMGSH : ARx_img_shadow_vis SEGS ARx.
Hypothesis HFHULL : ARx_frame_hull_vis SEGS ARx.
(* image fact, discharged at PI_prog_A by reflexivity (PAImg_prog.v:408 pa_lo := IMG_LO; pa_hi := IMG_TOP): the
   instance's image band is image A's (kept_at's image arms are per instance since 2026-10-29; WalkS7bR's ruling) *)
Hypothesis HPAB : pa_lo = IMG_LO /\ pa_hi = IMG_TOP.
(* alloc.c's six statics and fuzz_preset.c's g_own_ran_out (the ledger's globals, prh_pst, PRH_Base.v:752-755) are image bytes the runtime does not own, apart from errno, and none
   lies in the read-only band (YC1fPx's PST_ok; the S7b walk's pj_write takes the same texts; image facts) *)
Hypothesis PST_ok : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).
(* the memory invariant the walk carries: GENERIC (h-hpreset-7's 12:18Z ruling), instantiated once at the top as the
   YAkMemnorm keep; the walk crosses calls, so it also takes srr_inv_call (YSRrMemnorm, h-w6u-pre) *)
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Let RUN := @paj_run_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let RUNTO := @paj_run_to_x fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst prh_img_A) ARx _ LAWS.
Let NTRUNTO := SRr_run_to_pi_AJx B ARx LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx).
Local Notation AJR R := (ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx R).

(* the return site of put_string's calls lies in the listing's code range (by name: the slot of A_entry_put_string) *)
Lemma AF_ps_ret : 0 <= AF_put_string + 116 < 2 ^ 40 /\ (AF_put_string + 116) mod 2 = 0.
Proof.
unfold AF_put_string. rewrite (proj2 A_entry_put_string).
split; [split; vm_compute; congruence | reflexivity].
Qed.
(* every return site inside put_string (offset k < 884, the function's length) is a code pointer above 4096 *)
Lemma AF_ps_ret_k : forall k, 0 <= k < 884 -> k mod 2 = 0 ->
  (0 <= AF_put_string + k < 2 ^ 40 /\ (AF_put_string + k) mod 2 = 0) /\ 4096 <= BASE + (AF_put_string + k).
Proof.
intros k Hk Hk2. pose proof (pa_B_ok (L := A_prog_listing) (PAImg := PA)) as (HB0 & _).
assert (HAF : 4096 <= AF_put_string /\ AF_put_string mod 2 = 0 /\ AF_put_string < 2 ^ 39).
{ unfold AF_put_string. rewrite (proj2 A_entry_put_string). vm_compute. repeat split; congruence. }
split; [split; [lia|]|lia]. rewrite Zplus_mod, Hk2, (proj1 (proj2 HAF)). reflexivity.
Qed.
(* put_string's return sites (after frame_alloc_0, the five puts, memcpy, snprintf, strlen) lie below the ceiling
   (fpre's raZ bound), by PRW_StepKit.pa_slot_lt_ceil_b on a closed goal *)
Lemma ps_ret_lt_ceil : forall k, In k [116; 276; 428; 536; 560; 568; 584; 688; 708] ->
  BASE + (AF_put_string + k) < YM05.alloc_ceiling.
Proof.
intros k Hk.
assert (HkR : 0 <= k < 884 /\ k mod 2 = 0) by (cbn [In] in Hk; repeat destruct Hk as [<- | Hk]; try destruct Hk; split; lia || reflexivity).
destruct (AF_ps_ret_k k (proj1 HkR) (proj2 HkR)) as ((Hk40 & _) & _).
apply (pa_slot_lt_ceil_b (L := A_prog_listing) (PL := PL_prog_A) (PI := PA) (AF_put_string + k) Hk40).
cbn [In] in Hk; repeat destruct Hk as [<- | Hk]; try destruct Hk; vm_compute; reflexivity.
Qed.
(* the walk's stack budget covers its frame and each callee's need *)
Lemma STK_ps_facts : ESTACK + 208 <= STK_put_string /\ STK_put + 208 <= STK_put_string /\ 0 <= STK_put /\
  STK_RT_PRINTF + 208 <= STK_put_string /\ STK_RT_STR + 208 <= STK_put_string /\ STK_RT_ECALL + 208 <= STK_put_string.
Proof. vm_compute. repeat split; congruence. Qed.
(* the read-only view at a later memory: it agrees on the read-only bytes *)
Lemma ps_arodata_keep : forall (W W' : world SEGS) mem mem',
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof. intros W W' mem mem' HRO HK a Hro Ho He. rewrite (HK a Hro Ho He). exact (HRO a Hro Ho He). Qed.
(* a read-only bytes' home reads no ledger *)
Lemma kept_at_nil_lam : forall Lam p n, kept_at B [] p n -> kept_at B Lam p n.
Proof.
intros Lam p n [(b & m & Hin & _) | H]; [destruct Hin | right; exact H].
Qed.
(* read-only bytes are image bytes *)
Lemma in_roP_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hs & _ & Hlo & Hhi) | Hr]; [exists sg; split; [exact Hs | lia] | apply pa_relro_img; exact Hr].
Qed.

(* ---- byte transport: the facts the walk carries hold at a later memory whose view agrees on their bytes ---- *)
Lemma val_mem_kept_av : forall H H' (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H' m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hlt. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hk (a + Z.of_nat k) ltac:(lia))). exact (Hv k Hlt).
Qed.
Lemma garr8_kept_av : forall H H' (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H' m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept_av H H' m m'); [intros x Hx; apply Hk; cbn in Hx; lia | exact Hv].
Qed.
(* a byte away from the struct and from the buffer block is outside the writer's footprint *)
Lemma notin_cfp : forall o buf cap a,
  ~ (o <= a < o + 32) ->
  (cap <> 0 -> ~ (buf - cf_head <= a < buf - cf_head + req_size (cap + cf_head))) ->
  ~ inFP (prhWriter_cfp o buf cap) a.
Proof.
intros o buf cap a Ho Hb (r & Hr & Ha). unfold prhWriter_cfp, prhWriter_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|].
revert Hr. destruct (Z.eqb_spec cap 0) as [E0 | E0]; intros Hr; [destruct Hr|].
unfold ablocks_fp in Hr. cbn [map In fst snd] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. exact (Hb E0 Ha).
Qed.
(* a region kept across a call: its bytes agree and its write window is present after (two worlds) *)
Lemma region_kept_av2 : forall E (H H' : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m2 a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H' m2 a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m2 n b lo hi wlo whi cs Hn Hav Hpr.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hpr. exact Ha.
Qed.
Lemma kept_of_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
  forall a, P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF HP a Ha. destruct (HP a Ha) as [Hr Hn]. apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* a block's shadow (block_shadow) makes every byte of the block addressable *)
Lemma block_shadow_range : forall rd p n, block_shadow rd SHADOW_OFF p n -> range_addressable rd SHADOW_OFF p n.
Proof.
intros rd p n (Hp8 & Hn & Hc) x Hx.
assert (Hi : shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF p + (x / 8 - p / 8)).
{ unfold shadow_of_addr. lia. }
assert (Hb : 0 <= x / 8 - p / 8 < (n + 7) / 8) by lia.
rewrite Hi. exists (if (x / 8 - p / 8) <? n / 8 then 0 else n mod 8). split; [exact (Hc _ Hb)|].
destruct (Z.ltb_spec (x / 8 - p / 8) (n / 8)) as [Hlt | Hge]; [left; reflexivity|].
destruct (Z.eq_dec (n mod 8) 0) as [E0 | En0]; [left; exact E0|]. right. lia.
Qed.
(* a harness block of the ledger (prh_hblock) has its user bytes addressable and their shadow hull visible (the
   harness-block shadow law, AR_laws_x field 14) *)
Lemma hblock_shadow : forall ly S Hp W mem md a k,
  ARx ly S Hp W mem md -> prh_hblock (PA := PA) B ly S Hp W mem a k -> 0 < k ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a k /\ shadow_hull_vis (aview SEGS (w_H W) mem) a k.
Proof.
intros ly S Hp W mem md a k HAR (Hk & Hin & HinH & _ & _) Hk0.
pose proof (@cf_head_nonneg cp) as Hch.
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hin HinH) as [Hbs Hhull].
unfold req_size in *. destruct (Z.eqb_spec (k + cf_head) 0) as [E0 | _]; [lia|].
replace (a - cf_head + cf_head) with a in Hbs, Hhull by lia. replace (k + cf_head - cf_head) with k in Hbs, Hhull by lia.
split; [exact (block_shadow_range _ _ _ Hbs) | apply Hhull; lia].
Qed.
(* a visible shadow hull covers every sub-window's hull *)
Lemma hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof. intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *. lia. Qed.
(* the hull of a window inside the image band [IMG_LO + 64, IMG_TOP - 64) is visible (ARx_img_shadow_vis) *)
Lemma img_hull_vis : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> IMG_LO + 64 <= p -> p + n + 64 <= IMG_TOP -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md p n HAR Hlo Hhi Hn sh Hsh.
unfold shadow_addr in Hsh. unfold IMG_LO, IMG_TOP, SHADOW_OFF in *.
replace sh with (shadow_addr ((sh - SHADOW_OFF) * 8)) by (unfold shadow_addr, SHADOW_OFF; lia).
apply (HIMGSH ly S Hp W mem md _ HAR). unfold IMG_LO, IMG_TOP, SHADOW_OFF. lia.
Qed.
(* a registered zero-shadow range is in zero_shadow_ranges, and its bytes are addressable *)
Lemma zs_range : forall ly S Hp W mem md q m,
  ARx ly S Hp W mem md -> In (q, m) (as_zero_shadow B) -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q m.
Proof.
intros ly S Hp W mem md q m HAR Hin.
pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, m) HAR (or_intror Hin)) as Hz.
pose proof (proj1 (Forall_forall _ _) (aso_zshadow B ASO) (q, m) Hin) as (_ & _ & Hq & Hm & _).
exact (zero_shadow_range _ _ q m Hq Hm Hz).
Qed.
(* the ledger's parts, by the kit's named projections (PRH_Base Section ledger_proj) *)
Lemma ps_led_blocks : forall ly S Hp W mem Lam peak cnt fail ran {most own : Z},
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam.
Proof. intros ly S Hp W mem Lam peak cnt fail ran most own H. eapply prh_ledger_blocks. exact H. Qed.
Lemma ps_led_nodup : forall ly S Hp W mem Lam peak cnt fail ran {most own : Z},
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> NoDup (map fst Lam).
Proof. intros ly S Hp W mem Lam peak cnt fail ran most own H. eapply prh_ledger_nodup. exact H. Qed.
Lemma ps_led_cnt : forall ly S Hp W mem Lam peak cnt fail ran {most own : Z},
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= cnt < 2 ^ 64.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own H. apply prh_ledger_bounds in H. destruct H as (_ & _ & H & _). exact H.
Qed.
Lemma ps_led_fail : forall ly S Hp W mem Lam peak cnt fail ran {most own : Z},
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= fail < 2 ^ 64.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own H. apply prh_ledger_bounds in H. destruct H as (_ & _ & _ & H & _). exact H.
Qed.
(* the string's home (kept_at) gives its shadow facts at ANY state: a live harness block of the ledger, a registered
   read-only global (zero shadow), or read-only image bytes with zero or constant shadow cells *)
Lemma str_shadow_at : forall ly S Hp W mem md Lam peak cnt fail ran {most own : Z} p n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  kept_at B Lam p n -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR Hled Hk Hn.
destruct Hk as [(b & m & HinL & Hbp & Hpe) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hall)]];
  try (rewrite (proj1 HPAB) in Hlo; rewrite (proj2 HPAB) in Hhi).
- pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. pose proof (proj1 (Forall_forall _ _) Hall (b, m) HinL) as Hhb. cbn [fst snd] in Hhb.
  destruct (hblock_shadow ly S Hp W mem md b m HAR Hhb ltac:(lia)) as [Hra Hhu].
  split; [exact (range_addressable_sub _ _ b m p n Hra Hbp Hpe) | exact (hull_sub _ b m p n Hhu Hbp Hpe)].
- split; [|exact (img_hull_vis ly S Hp W mem md p n HAR Hlo Hhi Hn)].
  destruct Hzs as (q & m & Hin & Hqp & Hpe).
  exact (range_addressable_sub _ _ q m p n (zs_range ly S Hp W mem md q m HAR Hin) Hqp Hpe).
- split; [|exact (img_hull_vis ly S Hp W mem md p n HAR Hlo Hhi Hn)].
  intros x Hx. destruct (Hall x Hx) as (_ & _ & _ & [Hz | (v & Hc & Hv)]).
  + destruct Hz as (q & m & Hin & Hqp & Hpe).
    pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (q, m) HAR (or_intror Hin)) as Hz.
    pose proof (proj1 (Forall_forall _ _) (aso_zshadow B ASO) (q, m) Hin) as (_ & _ & Hq & Hm & _).
    cbn [fst snd] in *.
    exists 0. split; [|left; reflexivity].
    assert (Hix : shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF q + (x / 8 - q / 8)).
    { unfold shadow_of_addr. lia. }
    rewrite Hix. apply Hz. lia.
  + pose proof (alx_const_cells SEGS B ARx LAWS ly S Hp W mem md HAR) as Hcells.
    pose proof (proj1 (Forall_forall _ _) Hcells _ (Hc ly)) as Hcell.
    unfold cell_holds, z1, c1 in Hcell. cbn [c_at c_val c_w aeval] in Hcell.
    specialize (Hcell 0%nat ltac:(lia)).
    replace (shadow_addr x + Z.of_nat 0) with (shadow_addr x) in Hcell by lia.
    assert (Hlb : le_byte v 1 0 = v).
    { unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
      rewrite Z.shiftr_0_r, !Z.mod_small; destruct Hv as [-> | Hv]; lia. }
    rewrite Hlb in Hcell.
    exists v. split; [|destruct Hv as [-> | Hv]; [left; reflexivity | right; lia]].
    unfold shadow_of_addr. unfold shadow_addr in Hcell. exact Hcell.
Qed.
(* the writer state at o (prhWriter_out) at a later memory: its struct and text bytes agree; the buffer's shadow facts
   come from the later state's own ledger block and the harness-block shadow law *)
Lemma prhW_out_kept : forall W mem Lam o buf st W' mem' ly' S' Hp' md',
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  ARx ly' S' Hp' W' mem' md' ->
  (WriterApp.w_cap st <> 0 -> prh_hblock (PA := PA) B ly' S' Hp' W' mem' buf (WriterApp.w_cap st)) ->
  (forall a, o <= a < o + 28 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (WriterApp.w_cap st <> 0 -> forall a, buf <= a < buf + WriterApp.w_cap st ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  prhWriter_out (PA := PA) W' mem' Lam o buf st.
Proof.
intros W mem Lam o buf st W' mem' ly' S' Hp' md' Hout HAR' Hblk Ho Hb.
unfold prhWriter_out in *.
destruct Hout as (Ho8 & Hbuf & Hcap & V0 & V8 & V16 & V24 & Hf01 & Hbok & Hcase).
split; [exact Ho8|]. split; [exact Hbuf|]. split; [exact Hcap|].
split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Ho; cbn in Hx; lia | exact V0]|].
split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Ho; cbn in Hx; lia | exact V8]|].
split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Ho; cbn in Hx; lia | exact V16]|].
split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Ho; cbn in Hx; lia | exact V24]|].
split; [exact Hf01|]. split; [exact Hbok|].
- destruct Hcase as [Hz | (Hgrid & HinL & Hlen & Hbytes & Hsh)]; [left; exact Hz | right].
  assert (Hc0 : WriterApp.w_cap st <> 0) by (destruct Hgrid as (j & Hj & ->); pose proof (Z.pow_pos_nonneg 2 j); lia).
  split; [exact Hgrid|]. split; [exact HinL|]. split; [exact Hlen|]. split.
  + destruct Hbytes as (rest & Hrl & Hbytes). exists rest. split; [exact Hrl|].
    unfold bytes_at in *. apply (garr8_kept_av (w_H W) (w_H W') mem mem'); [|exact Hbytes].
    intros x Hx. apply (Hb Hc0). lia.
  + intros _. apply (hblock_shadow ly' S' Hp' W' mem' md' buf (WriterApp.w_cap st) HAR' (Hblk Hc0)).
    destruct Hgrid as (j & Hj & ->). pose proof (Z.pow_pos_nonneg 2 j). lia.
Qed.
(* the ledger at a later memory: the seven globals (#102 added g_most and g_own_ran_out) and every live block's head
   word agree, same blocks and heads *)
Lemma prh_ledger_kept : forall ly S Hp W mem Lam peak cnt fail ran {most own : Z} ly' S' W' mem',
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ablocks B ly' S' = ablocks B ly S ->
  (forall a, (pi_g_live <= a < pi_g_live + Z.of_nat pi_gz_live) \/ (pi_g_peak <= a < pi_g_peak + Z.of_nat pi_gz_peak) \/
     (pi_g_count <= a < pi_g_count + Z.of_nat pi_gz_count) \/ (pi_g_fail <= a < pi_g_fail + Z.of_nat pi_gz_fail) \/
     (pi_g_ran_out <= a < pi_g_ran_out + Z.of_nat pi_gz_ran_out) \/
     (pi_g_most <= a < pi_g_most + Z.of_nat pi_gz_most) \/
     (pi_g_own_ran_out <= a < pi_g_own_ran_out + Z.of_nat pi_gz_own_ran_out) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall b k a, In (b, k) Lam -> b - cf_head <= a < b - cf_head + 8 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly' S' Hp W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly' S' W' mem' Hled Eab Hg Hh.
pose proof Hled as G1. apply prh_ledger_live in G1. pose proof Hled as G2. apply prh_ledger_peak in G2.
pose proof Hled as G3. apply prh_ledger_count in G3. pose proof Hled as G4. apply prh_ledger_fail in G4.
pose proof Hled as G5. apply prh_ledger_ran in G5. pose proof Hled as Gr. apply prh_ledger_bounds in Gr.
pose proof Hled as Gm. apply prh_ledger_most in Gm. pose proof Hled as Go. apply prh_ledger_own in Go.
unfold prh_most in Gm. unfold prh_own in Go. destruct Gm as (Gm & Gm2). destruct Go as (Go & Go2).
pose proof Hled as Hnd. apply prh_ledger_nodup in Hnd. pose proof Hled as Hall. apply prh_ledger_blocks in Hall.
pose proof Hled as Hperm. apply prh_ledger_heads in Hperm.
unfold prh_ledger, prh_glob, prh_most, prh_own.
split; [|split; [exact Hnd|split; [|exact Hperm]]].
- split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact G1]|].
  split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact G2]|].
  split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact G3]|].
  split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact G4]|].
  split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact G5]|].
  split; [split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact Gm] | exact Gm2]|].
  split; [split; [apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply Hg; lia | exact Go] | exact Go2]|].
  exact Gr.
- rewrite Forall_forall in Hall |- *. intros [b k] Hin. specialize (Hall (b, k) Hin).
  unfold prh_hblock in *. cbn [fst snd] in *. destruct Hall as (Hk & HinB & HinH & Hal & Hv).
  split; [exact Hk|]. split; [rewrite Eab; exact HinB|]. split; [exact HinH|]. split; [exact Hal|].
  apply (val_mem_kept_av (w_H W) (w_H W') mem mem'); [intros x Hx; apply (Hh b k x Hin); cbn in Hx; lia | exact Hv].
Qed.

(* the symbolic entry state *)
Lemma ps_entry : forall STK ly S Hp W regs mem md ch o s,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 208 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s ->
  spZ regs <= o < 2 ^ 47 -> o mod 8 = 0 -> 4096 <= s < 2 ^ 47 ->
  st_ok_pi SEGS VAL (ps_E regs (as_uar_cell B)) ps_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_put_string)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PS_Bx ps_SH (ps_E regs (as_uar_cell B)) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch o s HPRE HSTK H10 H11 Ho Ho8 Hs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite Huar in Kgu.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_val_range (A_OBJ 0)) as RG. pose proof (pa_val_range (A_OBJ 12)) as RC. pose proof (pa_val_range (A_OBJ 1)) as RU.
destruct HOBJ as (D10 & D112). destruct HUARC as (U1 & U2 & U3 & U4).
pose proof (pa_segs_low _ (proj1 (Hobj 0 ltac:(lia)))) as L00. pose proof (pa_segs_low _ (proj1 (Hobj 7 ltac:(lia)))) as L07.
pose proof (pa_segs_low _ (proj1 (proj2 (Hobj 0 ltac:(lia))))) as L120. pose proof (pa_segs_low _ (proj1 (proj2 (Hobj 7 ltac:(lia))))) as L127.
pose proof (pa_segs_low _ (proj2 (proj2 (Hobj 0 ltac:(lia))))) as L10. pose proof (pa_segs_low _ (proj2 (proj2 (Hobj 7 ltac:(lia))))) as L17.
pose proof (pa_segs_low _ (U1 0 ltac:(lia))) as LU0. pose proof (pa_segs_low _ (U1 3 ltac:(lia))) as LU3.
rewrite Z.add_0_r in L00, L120, L10, LU0.
rewrite restrict_mkst_fx.
set (sp := spZ regs) in *.
set (uar := as_uar_cell B) in *.
set (E := ps_E regs uar).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 PS_SB; Z_to_bv 64 uar; Z_to_bv 64 (PS_R sp)]) k)
  by (intros k Hk; subst E; unfold ps_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 s) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 PS_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 uar) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (PS_R sp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold ps_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold ps_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EU : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold ps_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (Hsp : 2 ^ 46 <= sp <= 2 ^ 47) by (unfold alloc_ceiling in *; lia).
assert (HR : sp - 208 <= PS_R sp <= sp - 192 /\ PS_R sp mod 32 = 0).
{ unfold PS_R. pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)).
  assert ((sp - 192) mod 32 = 0 \/ (sp - 192) mod 32 = 16).
  { pose proof (Z.div_mod sp 16 ltac:(lia)). pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)). lia. }
  split; [lia|]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
split.
- unfold ps_ss0. apply pa_entry_st_ok_full.
  + unfold E, ps_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold probe_region, saved_region, got_regionP, bcell_regionP, uargot_region, uarcell_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) PS_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold PS_SB, SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EU RU). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) uar);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold IMG_LO, IMG_TOP in *; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgu).
    * rewrite (VB 33%nat uar E33) by (unfold IMG_LO, IMG_TOP in *; lia). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ uar 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold probe_region, saved_region, got_regionP, bcell_regionP, uargot_region, uarcell_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC),
      (VB (A_OBJ 1) (VAL (A_OBJ 1)) EU RU), (VB 33%nat uar E33) by (unfold IMG_LO, IMG_TOP in *; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold IMG_LO, IMG_TOP, alloc_ceiling in *. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [ps_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E32, E33, E34, !unsigned_lit_small by (unfold PS_SB, SHADOW_OFF, IMG_LO, IMG_TOP, alloc_ceiling in *; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold PS_SB, alloc_ceiling in *. repeat match goal with |- _ /\ _ => split end; lia.
    * cbn [ps_facts f_alias alias_ok]. split; [|exact I].
      assert (Esp : bv_unsigned (getr regs 2) = sp) by reflexivity.
      assert (HPR : 0 <= PS_R sp < 2 ^ 64) by (unfold PS_R; lia).
      assert (HPR1 : sp + -192 = sp - 192) by lia.
      apply U_inj. unfold PS_AND. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SOff, U_SLit, E2, E34, Z.add_0_r.
      unfold zcanon, M64. rewrite Esp, HPR1.
      replace ((-32) mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
      rewrite (Z.mod_small (sp - 192)) by lia.
      rewrite land_m32 by lia.
      rewrite unsigned_lit_small by lia.
      unfold PS_R. reflexivity.
- unfold sh_ok, ps_SH. constructor.
Qed.

(* ---- the put call sites (A 0x8847c, 0x88514, 0x885b0, 0x88618, 0x8862c) ---- *)
Variable CTX0 : list (list Z).
(* put's text (the kit's tput_specX, WalkS7a's walk): the ONE callee-text use of put in this file *)
Hypothesis PUT : tput_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0.

(* one put call from a state the walk's journal describes: aj_call_xWR (the engine's call of an fpostW callee over a
   world relation) at put's text, with put's window e1 := - oc reaching up to the walk's own window top sp0 (it holds
   the caller's struct). put reallocs its buffer when it grows (a crossing call): its text concludes SRr' with its
   journal at wle' SEGS RZ_cf, so the walk's journals and the conclusion here are at that relation *)
Lemma ps_put_call : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k
    regsc raw ch1 o s n buf (st : WriterApp.wst) (bs : list Z) Lam peak ran {most gown : Z} oc,
  AJR (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + oc -> oc mod 16 = 0 -> oc <= 0 -> 0 <= STK_put -> STK_put - oc <= STKc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + oc) (s0Z regsc) ch1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) -> sp0 + oc + 64 <= ly_stk_hi lyc ->
  (* fpre's FRM0-ENTRY at the call: the CURRENT float state's rounding mode is 0 *)
  YK0o.frm_zero (@YK11.fp_csr fx) ->
  room_live_cf Sc -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (* put's text takes the room positions' bound *)
  (length rp_os <= 4)%nat ->
  (* The batch kit's PRH_FnWriter.v d89d3c67b78c :421: put's consumer window *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 n ->
  sp0 + oc <= o -> o + 32 <= sp0 ->
  (* the chain from o at the call view (the kit's case 1, o >= put's sp + 16): an ARGUMENT, reported to the S7b walk
     2026-10-29 (after put #1 rewrote the struct, the entry-view chain does not transfer) *)
  sp0 + oc + 16 <= o ->
  (exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most gown ->
  src_rd W memc s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B lyc Sc Lam buf (WriterApp.w_cap st) s n ->
  (* put's run event (the kit's per-arm tput_specX, PRH_FnWriter d89d3c67b78c :464-465 at the cut) *)
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + n + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* The batch kit's :471: put's live room at each event of its all-granted run *)
  prh_live_evs Sc (prhWriter_evs [] st [bs]) ->
  fp_sub_x B STKc sp0 FP (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S own lyc Sc ->
  SRr' SEGS RZ_cf W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       AJR (wle' SEGS RZ_cf) STKc sp0 FP ly S Hp W0 mem0 md0 own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR (wle' SEGS RZ_cf) (STK_put + - oc) (sp0 + oc + - oc) (prhWriter_cfp o buf (WriterApp.w_cap st)) lyc Sc Hpc
         W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       (forall a, sp0 + oc <= a < sp0 + oc + - oc -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\
       ((room_live_cf S2 /\
         (prhWriter_grows st bs = false -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S2) /\
         (prhWriter_grows st bs = true -> forall f', val_mem SEGS (mrestrict (w_H W2) mem2) (o + 24) 4 f' ->
            (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S2) /\
            (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S2)) /\
        prhWriter_retg B lyc Sc Lam peak ran most gown o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2) /\
        (YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS mem2))).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regsc raw ch1 o s n
  buf st bs Lam peak ran most gown oc
  HJ Hsp Hoc16 Hoc0 HSTK0 HSTK Hgp Htp Hra Hraw Hra4 Hrac Hch Hro Hhi Hfz Hroom Hrp Hlen4 Hcons Hcl H10 H11 H12 Ho1 Ho2
  Ho16 Hch0
  Hout
  Hled
  Hsrc Hlen Hhome Hev
  Hwmax Hhead Hlive Hfp.
unfold SRr'.
eapply (@YCbqGcallW.aj_call_xWR fx rc SK SEGS B (@prh_pst prh_img_A) ARx _ LAWS segs_low (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf)
  (wle'_trans SEGS RZ_cf) W regsc memc (SIGMA AS_put)
  STKc sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc mdc k STK_put (- oc) (prhWriter_cfp o buf (WriterApp.w_cap st))
  oc raw ch1); try eassumption; try lia.
intros Hpre Hwin.
assert (Ho1' : spZ regsc <= o) by lia.
assert (Ho2' : o + 32 <= spZ regsc + - oc) by lia.
assert (Htop' : spZ regsc + 64 <= ly_stk_hi lyc) by lia.
assert (Hch0' : spZ regsc + 16 <= o -> exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
  exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
{ intros _. exact Hch0. }
assert (H16' : spZ regsc + 16 <= o) by lia.
assert (Hrac' : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite Hra; exact Hrac).
exact (PUT rp_sm rp_x rp_os rp_i rp_H0 rp_hist most gown lyc Sc Hpc W regsc memc mdc ch1 o s n (- oc) buf st bs Lam peak ran
  (conj Hpre (conj Hro (conj Htop' (conj Hrac' Hfz)))) Hroom Hrp Hlen4 Hcons Hcl H10 H11 H12 (or_introl H16') Hch0' Hwin
  Ho1' Ho2'
  Hout Hled
  Hsrc Hlen Hhome Hev Hwmax Hhead Hlive).
Qed.

(* ---- the pure escape model: the pieces still to put from byte i on, with the run [j, i) pending ---- *)
Lemma sr_nonspec : forall run c rest, WriterSpec.special c = false ->
  WriterSpec.spieces_run run (c :: rest) = WriterSpec.spieces_run (run ++ [c]) rest.
Proof. intros run c rest H. cbn [WriterSpec.spieces_run]. rewrite H. reflexivity. Qed.
Lemma sr_spec : forall run c rest, WriterSpec.special c = true ->
  WriterSpec.spieces_run run (c :: rest) = run :: WriterSpec.esc c :: WriterSpec.spieces_run [] rest.
Proof. intros run c rest H. cbn [WriterSpec.spieces_run]. rewrite H. reflexivity. Qed.
Lemma skipn_nth_cons : forall (l : list Z) i, (i < length l)%nat -> skipn i l = nth i l 0 :: skipn (S i) l.
Proof.
induction l as [|x l IH]; intros i Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.
Lemma firstn_skipn_snoc : forall (l : list Z) i j, (j <= i)%nat -> (i < length l)%nat ->
  firstn (S i - j) (skipn j l) = firstn (i - j) (skipn j l) ++ [nth i l 0].
Proof.
intros l i j Hji Hil.
replace (S i - j)%nat with (S (i - j)) by lia.
assert (Hn : nth i l 0 = nth (i - j) (skipn j l) 0) by (rewrite nth_skipn; f_equal; lia).
rewrite Hn. assert (Hl : (i - j < length (skipn j l))%nat) by (rewrite length_skipn; lia).
clear Hn Hji Hil. revert Hl. generalize (skipn j l) as m. generalize (i - j)%nat as k.
induction k as [|k IH]; intros m Hm; destruct m as [|y m]; cbn in Hm |- *; try lia; [reflexivity|].
f_equal. apply IH. lia.
Qed.

(* ---- the walk's context: the text's arguments at entry, the fake frame's position, the room position, the ledger's
   #102 cells (most, own: no put moves them) and the ENTRY float state x_fx (the float form's reference) ---- *)
Record psx := mkPSX {
  x_d : Z; x_ly : alayout; x_S : astate; x_Hp : list Z; x_W : world SEGS; x_regs : bvmap 5 word;
  x_mem : word -> option byte; x_md : Model; x_o : Z; x_s : Z; x_bs : list Z; x_buf : Z; x_st : WriterApp.wst;
  x_Lam : list (Z * Z); x_peak : Z; x_ran : Z;
  x_rpsm : list Z -> Z * Z; x_rpx : list Z; x_rpos : list (option nat * option nat * option nat); x_rpi : nat;
  x_rpH0 : list Z; x_rphist : list YG00.chunk; x_most : Z; x_own : Z; x_fx : YK11.FPState }.
Definition x_sp (X : psx) : Z := spZ (x_regs X).
Definition x_R (X : psx) : Z := PS_R (x_sp X).
(* the fake frame frame_alloc_0 returns, at position pos of class 0 *)
Definition x_F (X : psx) (pos : Z) : Z := frame_addr (x_ly X) 0 pos.
Definition x_FL (X : psx) (pos : Z) : Z := flag_addr (x_ly X) 0 pos.
Definition x_SHF (X : psx) (pos : Z) : Z := PS_SB + x_F X pos / 8.
Definition x_n (X : psx) : Z := Z.of_nat (length (x_bs X)).
Definition x_FP (X : psx) : list (Z * Z) := prhWriter_cfp (x_o X) (x_buf X) (WriterApp.w_cap (x_st X)).

(* the read-only escape sources and formats, by name: the addend of the PAddHi at put_string + 4 k in the generated
   listing, over the read-only band A_OBJ 2 (k = 65: .str.17, 85: .str.20, 87: .str.19, 89: .str.22, 91: .str.21,
   93: .str.18, from Listing_prog's slots; MEASURED) *)
Definition ps_lit (k : nat) : Z :=
  match nth (A_prog_slot AS_put_string + k) A_prog_listing (PW 0) with PAddHi _ _ _ _ off => off | _ => 0 end.
Definition ps_str (k : nat) : Z := VAL (A_OBJ 2) + ps_lit k.
(* the image fact of one read-only literal of put_string (HLIT17's form, IMAGE FACT discharged at PI_prog_A): its bytes
   and its read-only home at every state; the walk's files state each literal as `ps_lit_fact k bytes` *)
Definition ps_lit_fact (k : nat) (l : list Z) : Prop :=
  forall ly' S' Hp' (W' : world SEGS) m' md', ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (ps_str k) l /\ kept_at B [] (ps_str k) (Z.of_nat (length l)).
(* the double-quote literal .str.17 put_string puts twice (IMAGE FACT, discharged at PI_prog_A; pj_write's HLIT form):
   its byte is the image's, its shadow the read-only global's, at every state *)
Hypothesis HLIT17 : forall ly' S' Hp' (W' : world SEGS) m' md',
  ARx ly' S' Hp' W' m' md' ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m') ->
  src_rd W' m' (ps_str 65) [34] /\ kept_at B [] (ps_str 65) 1.

(* the saved registers' slots (the prologue's sd's at sp - 104 .. sp - 8): s11 .. s2, s1, s0, ra *)
Definition ps_saved_list : list (Z * Z) :=
  [(-104, 27); (-96, 26); (-88, 25); (-80, 24); (-72, 23); (-64, 22); (-56, 21); (-48, 20); (-40, 19); (-32, 18);
   (-24, 9); (-16, 8); (-8, 1)].
Definition ps_saved_ok (X : psx) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  Forall (fun p => rdword (aview SEGS (w_H Wc) memc) (x_sp X + fst p) =
                   Some (bv_unsigned (getr (x_regs X) (Z_to_bv 5 (snd p))))) ps_saved_list.

(* the walk's final post: the text's float form at the re-hiding relation, fpostWFR at wle' SEGS RZ_cf (the walk
   crosses put, which reallocs), at the text's inner Q (the batch kit's PRH_FnWriter.v :640-649: the writer
   with its outcomes ok and the EXACT advance under them), RELATIVE TO THE ENTRY float state x_fx (so it reads no
   float state of a Section: a segment that ends at any current fx' states it), with the generic invariant at the final
   memory; at Pm := the memnorm keep from the entry it is the text's fpostWFmR at wle' SEGS RZ_cf *)
Definition ps_Qin (X : psx) :=
  fun ly' S' Hp' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
    room_live_cf S' /\
    exists ok, prhWriter_ret_ok B ok (x_ly X) (x_S X) (x_Lam X) (x_peak X) (x_ran X) (x_most X) (x_own X) (x_o X)
      (x_buf X) (x_st X) (WriterSpec.spieces (x_bs X)) ly' S' Hp' W' regs' mem' md' /\
    (* The batch kit's PRH_FnWriter.v d89d3c67b78c :647, DEAD-PUTSTRING *)
    prh_granted ok (WriterApp.w_cnt (x_st X)) (WriterApp.w_fail (x_st X))
      (prhWriter_k ok (x_st X) (WriterSpec.spieces (x_bs X))) /\
    exists hist', PresetRoomPos.iface_room_pos (x_rpsm X) (x_rpx X) (x_rpos X)
      (x_rpi X + length (prhWriter_evs ok (x_st X) (WriterSpec.spieces (x_bs X))))%nat (x_rpH0 X) hist' S'.
Definition ps_Qfin (X : psx) : world SEGS -> config -> Prop :=
  fun W' c' =>
    fpostWFR (fx := x_fx X) B ARx SK (wle' SEGS RZ_cf) STK_put_string (x_d X) (x_FP X) (x_regs X) (x_ly X) (x_S X)
      (x_Hp X) (x_W X) (x_mem X) (x_md X) (ps_Qin X) W' c' /\ Pm (ms_mem (cfg_ms c')).
(* the text's premises at the entry, the kit's tput_string_specX verbatim, its fpre at the ENTRY float state x_fx (the
   entry segment takes `x_fx X = fx`; every later segment runs at a current float state and reads only the entry's) *)
Definition ps_pre (X : psx) (ch : list (Z * Z * Z)) : Prop :=
  fpre (fx := x_fx X) B ARx STK_put_string (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_regs X) (x_mem X) (x_md X) ch /\
  room_live_cf (x_S X) /\
  PresetRoomPos.iface_room_pos (x_rpsm X) (x_rpx X) (x_rpos X) (x_rpi X) (x_rpH0 X) (x_rphist X) (x_S X) /\
  prh_univ_closure B CTX0 /\
  getr (x_regs X) 10 = w64 (x_o X) /\ getr (x_regs X) 11 = w64 (x_s X) /\
  (x_sp X + 16 <= x_o X \/ x_o X = x_sp X + 8) /\
  (x_sp X + 16 <= x_o X ->
     exists ra, rdword (aview SEGS (w_H (x_W X)) (x_mem X)) (x_o X - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H (x_W X)) (x_mem X)) (x_o X - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) /\
  fwin (x_ly X) (x_W X) (x_regs X) (x_mem X) (x_d X) /\ x_sp X <= x_o X /\ x_o X + 32 <= x_sp X + x_d X /\
  prhWriter_out (x_W X) (x_mem X) (x_Lam X) (x_o X) (x_buf X) (x_st X) /\
  prh_ledger B (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_Lam X) (x_peak X) (WriterApp.w_cnt (x_st X))
    (WriterApp.w_fail (x_st X)) (x_ran X) (x_most X) (x_own X) /\
  cstr_ok (x_W X) (x_mem X) (x_s X) (x_bs X) /\
  kept_at B (x_Lam X) (x_s X) (x_n X + 1) /\
  (WriterApp.w_cap (x_st X) = 0 \/ x_s X + x_n X + 1 <= x_buf X \/ x_buf X + WriterApp.w_cap (x_st X) <= x_s X) /\
  Z.of_nat (length (frames (x_S X))) < fs_frames 0 /\
  Z.of_nat (length (WriterApp.w_text (x_st X))) + Z.of_nat (length (WriterSpec.wstr (x_bs X))) + 1 <= prhWriter_WMAX /\
  prhWriter_WMAX + cf_head < cf_malloc_max /\
  (* The batch kit's :636: the live room at each event of its all-granted run (replaces the LIVE_put_string sum) *)
  prh_live_evs (x_S X) (prhWriter_evs [] (x_st X) (WriterSpec.spieces (x_bs X))) /\
  (* The batch kit's :584: its consumer window *)
  PRH_Base.prh_cons_from (x_rpsm X) (x_rpx X) (x_rpos X) (x_rpi X)
    (length (prhWriter_evs [] (x_st X) (WriterSpec.spieces (x_bs X)))) /\
  (* ITS RUN EVENTS, the kit's entry premise (PRH_FnWriter d89d3c67b78c at the cut): the run's next events are those of its puts,
     all granted *)
  prh_run_at (x_rpsm X) (x_rpx X) (x_rpos X) (x_rpi X) (prhWriter_evs [] (x_st X) (WriterSpec.spieces (x_bs X))) /\
  (* the room positions' bound (the text's premise after the re-hiding move; put's text takes it) *)
  (length (x_rpos X) <= 4)%nat.

(* the bytes [o - 16, o) at or above the entry sp, kept from the entry *)
Definition ps_okeep (X : psx) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall a, x_o X - 16 <= a < x_o X -> x_sp X <= a ->
    aview SEGS (w_H Wc) memc a = aview SEGS (w_H (x_W X)) (x_mem X) a.

(* the caller's window [sp, sp + d) off the entry footprint, kept from the entry (fpostW's window clause) *)
Definition ps_wkeep (X : psx) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
  forall a, x_sp X <= a < x_sp X + x_d X -> ~ inFP (x_FP X) a ->
    aview SEGS (w_H Wc) memc a = aview SEGS (w_H (x_W X)) (x_mem X) a.

(* the CURRENT float state (this Section's fx) against the entry's x_fx: the rounding mode is 0 and the callee-saved f
   registers are the entry's (the internal file REFIT-WRITER.md's float-threading design, point 2); a float-changing call moves it to fx' *)
Definition ps_float (X : psx) : Prop := YK0o.frm_zero (@YK11.fp_csr fx) /\ fregs_kept_x (x_fx X) fx.
(* what every join point carries about the current state (lyc Sc Hpc Wc memc mdc kc): the journal from the entry with
   the frame owned, the frame layout, the saved slots, the frame's flag-cell word, the string, the writer after the
   pieces P (prhWriter_ret opened, with the string's home at the current Lam and buffer, and the room position at the
   EXACT advance under the same outcomes ok), the room, the read-only view, the caller's window, the float state *)
Definition ps_common (X : psx) (pos : Z) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS) (memc : word -> option byte)
  mdc kc : Prop :=
  AJ (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc mdc kc /\
  ps_saved_ok X Wc memc /\
  rdword (aview SEGS (w_H Wc) memc) (x_F X pos + 56) = Some (x_FL X pos) /\
  ps_okeep X Wc memc /\
  Pm memc /\
  (exists ok ranc bufc Lamc peakc,
     (prh_oks ok (WriterApp.w_cnt (x_st X)) (WriterApp.w_fail (x_st X)) (prhWriter_k ok (x_st X) P)
        (prhWriter_reqs ok (x_st X) P) (x_most X) (x_ran X) ranc /\
      prh_granted ok (WriterApp.w_cnt (x_st X)) (WriterApp.w_fail (x_st X)) (prhWriter_k ok (x_st X) P)) /\
     prhWriter_out Wc memc Lamc (x_o X) bufc (prhWriter_putN ok (x_st X) P) /\
     prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (x_st X) P))
       (WriterApp.w_fail (prhWriter_putN ok (x_st X) P)) ranc (x_most X) (x_own X) /\
     prhWriter_blk B (x_ly X) (x_S X) (x_Lam X) (x_peak X) (x_buf X) (x_st X) lyc Sc Lamc peakc bufc
       (prhWriter_putN ok (x_st X) P) /\
     kept_at B Lamc (x_s X) (x_n X + 1) /\
     (forall b m, In (b, m) (x_Lam X) -> b <= x_s X -> x_s X + x_n X + 1 <= b + m -> In (b, m) Lamc) /\
     (WriterApp.w_cap (prhWriter_putN ok (x_st X) P) = 0 \/ x_s X + x_n X + 1 <= bufc \/
      bufc + WriterApp.w_cap (prhWriter_putN ok (x_st X) P) <= x_s X) /\
     exists rp_hist', PresetRoomPos.iface_room_pos (x_rpsm X) (x_rpx X) (x_rpos X)
       (x_rpi X + length (prhWriter_evs ok (x_st X) P))%nat (x_rpH0 X) rp_hist' Sc) /\
  room_live_cf Sc /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
  ps_wkeep X Wc memc /\
  ps_float X.
(* ps_common over a world relation R (its journal at R, ajournal_xR R): a COPY of ps_common's body beside it, because
   proof lines in other files unfold ps_common and read its body; ps_common_R_wle (by reflexivity) checks that
   ps_common IS ps_commonR at wle. Every join after the first put (a crossing call: put reallocs when it grows) states
   it at wle' SEGS RZ_cf; ps_commonR_mono lifts a join at wle to wle' (with wle_wle') *)
Definition ps_commonR (R : world SEGS -> world SEGS -> Prop) (X : psx) (pos : Z) (P : list (list Z)) lyc Sc Hpc
  (Wc : world SEGS) (memc : word -> option byte) mdc kc : Prop :=
  AJR R (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc mdc kc /\
  ps_saved_ok X Wc memc /\
  rdword (aview SEGS (w_H Wc) memc) (x_F X pos + 56) = Some (x_FL X pos) /\
  ps_okeep X Wc memc /\
  Pm memc /\
  (exists ok ranc bufc Lamc peakc,
     (prh_oks ok (WriterApp.w_cnt (x_st X)) (WriterApp.w_fail (x_st X)) (prhWriter_k ok (x_st X) P)
        (prhWriter_reqs ok (x_st X) P) (x_most X) (x_ran X) ranc /\
      prh_granted ok (WriterApp.w_cnt (x_st X)) (WriterApp.w_fail (x_st X)) (prhWriter_k ok (x_st X) P)) /\
     prhWriter_out Wc memc Lamc (x_o X) bufc (prhWriter_putN ok (x_st X) P) /\
     prh_ledger B lyc Sc Hpc Wc memc Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (x_st X) P))
       (WriterApp.w_fail (prhWriter_putN ok (x_st X) P)) ranc (x_most X) (x_own X) /\
     prhWriter_blk B (x_ly X) (x_S X) (x_Lam X) (x_peak X) (x_buf X) (x_st X) lyc Sc Lamc peakc bufc
       (prhWriter_putN ok (x_st X) P) /\
     kept_at B Lamc (x_s X) (x_n X + 1) /\
     (forall b m, In (b, m) (x_Lam X) -> b <= x_s X -> x_s X + x_n X + 1 <= b + m -> In (b, m) Lamc) /\
     (WriterApp.w_cap (prhWriter_putN ok (x_st X) P) = 0 \/ x_s X + x_n X + 1 <= bufc \/
      bufc + WriterApp.w_cap (prhWriter_putN ok (x_st X) P) <= x_s X) /\
     exists rp_hist', PresetRoomPos.iface_room_pos (x_rpsm X) (x_rpx X) (x_rpos X)
       (x_rpi X + length (prhWriter_evs ok (x_st X) P))%nat (x_rpH0 X) rp_hist' Sc) /\
  room_live_cf Sc /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) memc) /\
  ps_wkeep X Wc memc /\
  ps_float X.
Lemma ps_common_R_wle : forall X pos P lyc Sc Hpc Wc memc mdc kc,
  ps_common X pos P lyc Sc Hpc Wc memc mdc kc = ps_commonR (@wle SEGS) X pos P lyc Sc Hpc Wc memc mdc kc.
Proof. reflexivity. Qed.
(* a join at R1 is a join at every R2 that contains R1 (only the journal's world conjunct reads R) *)
Lemma ps_commonR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall X pos P lyc Sc Hpc Wc memc mdc kc,
  ps_commonR R1 X pos P lyc Sc Hpc Wc memc mdc kc -> ps_commonR R2 X pos P lyc Sc Hpc Wc memc mdc kc.
Proof.
intros R1 R2 H12 X pos P lyc Sc Hpc Wc memc mdc kc (HJ & Hr). split; [|exact Hr].
unfold ajournal_xR in *. eapply ajournal_xwR_mono; [exact H12 | exact HJ].
Qed.

(* the four joins below (ps_head, ps_tail, ps_esc, ps_next) lie after the first put, the opening quote: their join
   invariant is ps_commonR at wle' SEGS RZ_cf *)

(* the loop head (A 0x884ec): byte i is the current one (nonzero), the run [j, i) is pending; the registers and the
   frame slots the loop reads *)
Definition ps_head (X : psx) (pos : Z) (i j : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc /\
  (j <= i < length (x_bs X))%nat /\
  [34] :: WriterSpec.spieces_run [] (x_bs X) =
    P ++ WriterSpec.spieces_run (firstn (i - j) (skipn j (x_bs X))) (skipn i (x_bs X)) /\
  getr regsc 2 = w64 (x_R X) /\ getr regsc 3 = getr (x_regs X) 3 /\ getr regsc 4 = getr (x_regs X) 4 /\
  getr regsc 8 = w64 (x_sp X) /\ getr regsc 9 = w64 (x_R X) /\ getr regsc 18 = w64 (nth i (x_bs X) 0) /\
  getr regsc 19 = w64 (x_o X) /\ getr regsc 20 = w64 (x_s X + Z.of_nat i + 1) /\
  getr regsc 21 = w64 (x_F X pos + 32) /\ getr regsc 22 = w64 (x_SHF X pos) /\ getr regsc 23 = w64 PS_SB /\
  getr regsc 24 = w64 (x_s X + Z.of_nat i) /\ getr regsc 25 = w64 34 /\ getr regsc 26 = w64 (x_s X + Z.of_nat j) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 8) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 16) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 24) = Some (ps_str 91) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 32) = Some (ps_str 89) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 40) = Some (ps_str 87) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 48) = Some (ps_str 85) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 56) = Some (ps_str 93).

(* the tail join (A 0x8860c): the string is consumed, the run [j, n) is pending *)
Definition ps_tail (X : psx) (pos : Z) (j : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc /\
  (j <= length (x_bs X))%nat /\
  [34] :: WriterSpec.spieces_run [] (x_bs X) = P ++ [skipn j (x_bs X)] /\
  getr regsc 2 = w64 (x_R X) /\ getr regsc 3 = getr (x_regs X) 3 /\ getr regsc 4 = getr (x_regs X) 4 /\
  getr regsc 8 = w64 (x_sp X) /\ getr regsc 9 = w64 (x_R X) /\ getr regsc 19 = w64 (x_o X) /\
  getr regsc 20 = w64 (x_s X + x_n X) /\ getr regsc 21 = w64 (x_F X pos) /\ getr regsc 22 = w64 (x_SHF X pos) /\
  getr regsc 24 = w64 (x_F X pos) /\ getr regsc 26 = w64 (x_s X + Z.of_nat j).

(* the escape join (A 0x88518, the return of the run put at 0x88514): byte i is special, the run [j, i) is put (in
   P), u's shadow granule is unpoisoned (0), s11 holds the byte *)
Definition ps_esc (X : psx) (pos : Z) (i : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc /\
  (i < length (x_bs X))%nat /\ WriterSpec.special (nth i (x_bs X) 0) = true /\
  [34] :: WriterSpec.spieces_run [] (x_bs X) =
    P ++ WriterSpec.esc (nth i (x_bs X) 0) :: WriterSpec.spieces_run [] (skipn (S i) (x_bs X)) /\
  getr regsc 2 = w64 (x_R X) /\ getr regsc 3 = getr (x_regs X) 3 /\ getr regsc 4 = getr (x_regs X) 4 /\
  getr regsc 8 = w64 (x_sp X) /\ getr regsc 9 = w64 (x_R X) /\ getr regsc 18 = w64 (nth i (x_bs X) 0) /\
  getr regsc 19 = w64 (x_o X) /\ getr regsc 20 = w64 (x_s X + Z.of_nat i + 1) /\
  getr regsc 21 = w64 (x_F X pos + 32) /\ getr regsc 22 = w64 (x_SHF X pos) /\ getr regsc 23 = w64 PS_SB /\
  getr regsc 24 = w64 (x_s X + Z.of_nat i) /\ getr regsc 25 = w64 34 /\ getr regsc 27 = w64 (nth i (x_bs X) 0) /\
  aview SEGS (w_H Wc) memc (x_SHF X pos + 4) = Some 0 /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 8) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 16) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 24) = Some (ps_str 91) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 32) = Some (ps_str 89) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 40) = Some (ps_str 87) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 48) = Some (ps_str 85) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 56) = Some (ps_str 93).

(* the re-poison join (A 0x885b8): byte i is consumed, the run [j, i + 1) is pending (j = i + 1 after an escape) *)
Definition ps_next (X : psx) (pos : Z) (i j : nat) (P : list (list Z)) lyc Sc Hpc (Wc : world SEGS)
  (regsc : bvmap 5 word) (memc : word -> option byte) mdc kc : Prop :=
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc /\
  (j <= S i)%nat /\ (i < length (x_bs X))%nat /\
  [34] :: WriterSpec.spieces_run [] (x_bs X) =
    P ++ WriterSpec.spieces_run (firstn (S i - j) (skipn j (x_bs X))) (skipn (S i) (x_bs X)) /\
  getr regsc 2 = w64 (x_R X) /\ getr regsc 3 = getr (x_regs X) 3 /\ getr regsc 4 = getr (x_regs X) 4 /\
  getr regsc 8 = w64 (x_sp X) /\ getr regsc 9 = w64 (x_R X) /\
  getr regsc 19 = w64 (x_o X) /\ getr regsc 20 = w64 (x_s X + Z.of_nat i + 1) /\
  getr regsc 21 = w64 (x_F X pos + 32) /\ getr regsc 22 = w64 (x_SHF X pos) /\ getr regsc 23 = w64 PS_SB /\
  getr regsc 24 = w64 (x_s X + Z.of_nat i) /\ getr regsc 25 = w64 34 /\ getr regsc 26 = w64 (x_s X + Z.of_nat j) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 8) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 16) = Some (x_F X pos) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 24) = Some (ps_str 91) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 32) = Some (ps_str 89) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 40) = Some (ps_str 87) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 48) = Some (ps_str 85) /\
  rdword (aview SEGS (w_H Wc) memc) (x_R X + 56) = Some (ps_str 93).

(* the ledger's seven globals are the program-written statics (prh_pst: alloc.c's six with #102's g_most, and
   fuzz_preset.c's g_own_ran_out) *)
Lemma gcell_pst : forall a,
  (pi_g_live <= a < pi_g_live + Z.of_nat pi_gz_live) \/ (pi_g_peak <= a < pi_g_peak + Z.of_nat pi_gz_peak) \/
  (pi_g_count <= a < pi_g_count + Z.of_nat pi_gz_count) \/ (pi_g_fail <= a < pi_g_fail + Z.of_nat pi_gz_fail) \/
  (pi_g_ran_out <= a < pi_g_ran_out + Z.of_nat pi_gz_ran_out) \/
  (pi_g_most <= a < pi_g_most + Z.of_nat pi_gz_most) \/
  (pi_g_own_ran_out <= a < pi_g_own_ran_out + Z.of_nat pi_gz_own_ran_out) -> Exists (in_zr a) (@prh_pst prh_img_A).
Proof.
intros a H. unfold prh_pst.
destruct H as [H|[H|[H|[H|[H|[H|H]]]]]];
  [ apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | do 2 apply Exists_cons_tl; apply Exists_cons_hd
  | do 3 apply Exists_cons_tl; apply Exists_cons_hd | do 4 apply Exists_cons_tl; apply Exists_cons_hd
  | do 5 apply Exists_cons_tl; apply Exists_cons_hd | do 6 apply Exists_cons_tl; apply Exists_cons_hd ];
  unfold in_zr; cbn [fst snd]; exact H.
Qed.
(* the whole string has its two quotes *)
Lemma wstr_len2 : forall bs, (2 <= length (WriterSpec.wstr bs))%nat.
Proof.
intros bs. unfold WriterSpec.wstr, WriterSpec.spieces. cbn [concat]. rewrite concat_app. cbn [concat].
rewrite !length_app. cbn [length]. lia.
Qed.


(* ---- the string's home across the writer's runs ---- *)
Lemma pairwise_In_neq : forall {X} (R : X -> X -> Prop) l x y,
  (forall a b, R a b -> R b a) -> pairwise R l -> In x l -> In y l -> x <> y -> R x y.
Proof.
intros X R l x y Hs. induction l as [|z l IH]; intros Hp Hx Hy Hne; [destruct Hx|].
cbn [pairwise] in Hp. destruct Hp as (Hf & Hp). rewrite Forall_forall in Hf.
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. apply Hne. reflexivity.
- exact (Hf y Hy).
- apply Hs. exact (Hf x Hx).
- exact (IH Hp Hx Hy Hne).
Qed.
(* two distinct blocks of the ledger lie apart, heads included (the separation law) *)
Lemma ledger_blocks_disj : forall ly S Hp W mem md Lam peak cnt fail ran {most own : Z} b1 m1 b2 m2,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b1, m1) Lam -> In (b2, m2) Lam -> b1 <> b2 ->
  b1 + m1 <= b2 - cf_head \/ b2 + m2 <= b1 - cf_head.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b1 m1 b2 m2 HAR Hled H1 H2 Hne.
pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
destruct (Hall _ H1) as (Hk1 & HB1 & _). destruct (Hall _ H2) as (Hk2 & HB2 & _). cbn [fst snd] in *.
pose proof (@cf_head_nonneg cp) as Hh.
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (Hpw & _).
assert (Hz : zdisjoint (b1 - cf_head, req_size (m1 + cf_head)) (b2 - cf_head, req_size (m2 + cf_head))).
{ apply (pairwise_In_neq zdisjoint _ _ _ ltac:(intros a0 b0 H0; unfold zdisjoint in *; lia) Hpw).
  - apply in_or_app. left. exact (in_map (fun b => (fst b, req_size (snd b))) _ _ HB1).
  - apply in_or_app. left. exact (in_map (fun b => (fst b, req_size (snd b))) _ _ HB2).
  - intros Heq. injection Heq as Heq _. lia. }
assert (Hm1 : 0 <= m1 + cf_head) by (clear - Hk1 Hh; lia). assert (Hm2 : 0 <= m2 + cf_head) by (clear - Hk2 Hh; lia).
pose proof (req_size_pos (m1 + cf_head) Hm1) as R1. pose proof (req_size_pos (m2 + cf_head) Hm2) as R2.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
Qed.
(* the blocks arm keeps every live block of the ledger that is not the writer's old buffer *)
Lemma blk_kept_at : forall ly S Lam peak buf st ly' S' Lam' peak' buf' st' p n,
  prhWriter_blk B ly S Lam peak buf st ly' S' Lam' peak' buf' st' -> 0 < n ->
  (WriterApp.w_cap st = 0 \/ p + n <= buf \/ buf + WriterApp.w_cap st <= p) ->
  forall b m, In (b, m) Lam -> b <= p -> p + n <= b + m -> In (b, m) Lam'.
Proof.
intros ly S Lam peak buf st ly' S' Lam' peak' buf' st' p n Hblk Hn Hd b m Hin Hb Hp.
destruct Hblk as [(_ & _ & -> & _ & _) | (Hlt & l1 & l2 & b1 & b2 & Hc & -> & _ & _)]; [exact Hin|].
right. destruct Hc as [(_ & -> & -> & _ & _) | (Hc0 & ELam & _)]; [exact Hin|].
rewrite ELam in Hin. apply in_app_or in Hin. apply in_or_app.
destruct Hin as [H | [Heq | H]]; [left; exact H | | right; exact H].
injection Heq as E1 E2. exfalso. lia.
Qed.
(* the string stays apart from the writer's buffer across a run of puts *)
Lemma blk_src_disj : forall ly S Lam peak buf st ly' S' Hp' W' mem' md' Lam' peak' buf' st' cnt fail ran {most own : Z}
    p n,
  prhWriter_blk B ly S Lam peak buf st ly' S' Lam' peak' buf' st' ->
  ARx ly' S' Hp' W' mem' md' -> prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt fail ran most own ->
  kept_at B Lam p n -> 0 < n ->
  (WriterApp.w_cap st = 0 \/ p + n <= buf \/ buf + WriterApp.w_cap st <= p) ->
  WriterApp.w_cap st' = 0 \/ p + n <= buf' \/ buf' + WriterApp.w_cap st' <= p.
Proof.
intros ly S Lam peak buf st ly' S' Hp' W' mem' md' Lam' peak' buf' st' cnt fail ran most own p n Hblk HAR Hled Hk Hn Hd.
destruct Hblk as [(Ec & Eb & _ & _ & _) | (Hlt & l1 & l2 & b1 & b2 & Hc & EL & _ & _)].
{ rewrite Ec, Eb. exact Hd. }
destruct (Z.eq_dec (WriterApp.w_cap st') 0) as [Z0 | NZ]; [left; exact Z0|].
right. pose proof (@cf_head_nonneg cp) as Hh.
assert (HinB' : In (buf', WriterApp.w_cap st') Lam') by (rewrite EL; left; reflexivity).
pose proof (ps_led_nodup _ _ _ _ _ _ _ _ _ _ Hled) as Hnd. pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall'. rewrite Forall_forall in Hall'.
destruct (Hall' _ HinB') as (Hk0 & HinBB & _). cbn [fst snd] in Hk0, HinBB.
destruct Hk as [(b & m & Hin & Hb & Hp) | [(_ & Hlo & Hhi & Hall) | (Hlo & Hhi & Hall)]].
- assert (Hin12 : In (b, m) (l1 ++ l2)).
  { destruct Hc as [(_ & -> & -> & _ & _) | (Hc0 & ELam & _)]; [exact Hin|].
    rewrite ELam in Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [H | [Heq | H]]; [left; exact H | | right; exact H].
    injection Heq as E1 E2. exfalso. lia. }
  assert (Hne : b <> buf').
  { intros Eb. rewrite EL in Hnd. cbn [map fst] in Hnd. inversion Hnd as [|x0 l0 Hnin Hnd0].
    apply Hnin. rewrite <- Eb. pose proof (in_map fst (l1 ++ l2) (b, m) Hin12) as Hx. cbn [fst] in Hx.
    first [ exact Hx | apply list_elem_of_In; exact Hx | apply elem_of_list_In; exact Hx ]. }
  assert (HinL' : In (b, m) Lam') by (rewrite EL; right; exact Hin12).
  pose proof (ledger_blocks_disj ly' S' Hp' W' mem' md' Lam' peak' cnt fail ran b m buf' (WriterApp.w_cap st')
    HAR Hled HinL' HinB' Hne) as Hdj.
  clear - Hdj Hb Hp Hh. lia.
- destruct (Z_le_gt_dec (p + n) buf') as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (buf' + WriterApp.w_cap st') p) as [H2 | H2]; [right; exact H2|]. exfalso.
  assert (Hmx : p <= Z.max p buf' < p + n) by (clear - H1 H2 Hn; lia).
  destruct (Hall (Z.max p buf') Hmx) as (Hro & _).
  assert (Hcz : 0 <= WriterApp.w_cap st' + cf_head) by (clear - Hk0 Hh; lia).
  pose proof (req_size_pos _ Hcz) as Rq.
  assert (Hrg : buf' - cf_head <= Z.max p buf' < buf' - cf_head + req_size (WriterApp.w_cap st' + cf_head))
    by (clear - Rq H1 H2 Hh Hk0 NZ; lia).
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly' S' Hp' W' mem' md' (Z.max p buf') HAR
    (or_introl (ex_intro _ (buf' - cf_head) (ex_intro _ (WriterApp.w_cap st' + cf_head) (conj HinBB Hrg)))))).
  exact (in_roP_img _ Hro).
- destruct (Z_le_gt_dec (p + n) buf') as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (buf' + WriterApp.w_cap st') p) as [H2 | H2]; [right; exact H2|]. exfalso.
  assert (Hmx : p <= Z.max p buf' < p + n) by (clear - H1 H2 Hn; lia).
  destruct (Hall (Z.max p buf') Hmx) as (Hro & _).
  assert (Hcz : 0 <= WriterApp.w_cap st' + cf_head) by (clear - Hk0 Hh; lia).
  pose proof (req_size_pos _ Hcz) as Rq.
  assert (Hrg : buf' - cf_head <= Z.max p buf' < buf' - cf_head + req_size (WriterApp.w_cap st' + cf_head))
    by (clear - Rq H1 H2 Hh Hk0 NZ; lia).
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly' S' Hp' W' mem' md' (Z.max p buf') HAR
    (or_introl (ex_intro _ (buf' - cf_head) (ex_intro _ (WriterApp.w_cap st' + cf_head) (conj HinBB Hrg)))))).
  exact (in_roP_img _ Hro).
Qed.
(* the string's bytes at a later state of the walk, from the entry, through the walk's journal at a world relation R
   (after a put: R := wle' SEGS RZ_cf): a live block it lives in is a block of both states and outside the footprint;
   a read-only image byte is kept outright *)
Lemma cstr_from_entryR : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc
    memc mdc kc Lam0 peak0 c0 f0 r0 {m0 o0 : Z} Lamc peakc cc fc rc' {mc oc : Z} s bs,
  AJR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B ly S Hp W mem Lam0 peak0 c0 f0 r0 m0 o0 -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cc fc rc' mc oc ->
  cstr W mem s bs -> kept_at B Lam0 s (Z.of_nat (length bs) + 1) ->
  (forall b m, In (b, m) Lam0 -> b <= s -> s + Z.of_nat (length bs) + 1 <= b + m -> In (b, m) Lamc) ->
  (forall a, s <= a < s + Z.of_nat (length bs) + 1 -> ~ inFP FP a) -> ~ YI16.sink_open_fp FP ->
  cstr Wc memc s bs.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc Lam0 peak0 c0 f0 r0 m0 o0 Lamc peakc cc fc rc' mc oc
  s bs HJ Hl0 Hlc Hc Hk Hlive Hnfp Hcl.
pose proof (ajxR_blk HJ) as HKB. pose proof (ajxR_img HJ) as HKI.
assert (Hkeep : forall a, s <= a < s + Z.of_nat (length bs) + 1 -> aview SEGS (w_H Wc) memc a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (@cf_head_nonneg cp) as Hh.
  assert (Ha' : s <= a < s + (Z.of_nat (length bs) + 1)) by (clear - Ha; lia).
  destruct Hk as [(b & m & Hin & Hb & Hpe) | [(_ & _ & _ & Hall) | (_ & _ & Hall)]].
  - pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hl0) as Hall0. rewrite Forall_forall in Hall0.
    destruct (Hall0 _ Hin) as (Hk0 & HB0 & _). cbn [fst snd] in Hk0, HB0.
    pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hlc) as Hallc. rewrite Forall_forall in Hallc.
    assert (Hpe' : s + Z.of_nat (length bs) + 1 <= b + m) by (clear - Hpe; lia).
    destruct (Hallc _ (Hlive b m Hin Hb Hpe')) as (_ & HBc & _). cbn [fst snd] in HBc.
    assert (Hmz : 0 <= m + cf_head) by (clear - Hk0 Hh; lia). pose proof (req_size_pos _ Hmz) as Rq.
    replace a with ((b - cf_head) + (a - (b - cf_head))) by (clear; lia).
    apply (HKB _ _ _ HB0 HBc); [clear - Ha Hb Hpe Rq Hh; lia|].
    replace (b - cf_head + (a - (b - cf_head))) with a by (clear; lia). exact (Hnfp a Ha).
  - destruct (Hall a Ha') as (Hro & Ho & He).
    apply HKI; [exact (in_roP_img a Hro) | exact Ho | exact He | exact (HPSTRO a Hro) | exact (fp_spares_closed FP a Hcl)].
  - destruct (Hall a Ha') as (Hro & Ho & He & _).
    apply HKI; [exact (in_roP_img a Hro) | exact Ho | exact He | exact (HPSTRO a Hro) | exact (fp_spares_closed FP a Hcl)]. }
destruct Hc as (Hg & Hnz). split; [|exact Hnz].
apply (garr8_kept_av (w_H W) (w_H Wc) mem memc); [|exact Hg].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hkeep. lia.
Qed.
(* cstr_from_entryR at wle *)
Lemma cstr_from_entry : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc Lam0 peak0 c0 f0 r0
    {m0 o0 : Z} Lamc peakc cc fc rc' {mc oc : Z} s bs,
  AJ STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc kc ->
  prh_ledger B ly S Hp W mem Lam0 peak0 c0 f0 r0 m0 o0 -> prh_ledger B lyc Sc Hpc Wc memc Lamc peakc cc fc rc' mc oc ->
  cstr W mem s bs -> kept_at B Lam0 s (Z.of_nat (length bs) + 1) ->
  (forall b m, In (b, m) Lam0 -> b <= s -> s + Z.of_nat (length bs) + 1 <= b + m -> In (b, m) Lamc) ->
  (forall a, s <= a < s + Z.of_nat (length bs) + 1 -> ~ inFP FP a) -> ~ YI16.sink_open_fp FP ->
  cstr Wc memc s bs.
Proof. exact (cstr_from_entryR (@wle SEGS)). Qed.
(* a string's home lies between 4096 and the allocation ceiling *)
Lemma kept_at_bounds : forall ly S Hp W mem md Lam peak cnt fail ran {most own : Z} p n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> kept_at B Lam p n -> 0 < n ->
  4096 <= p /\ p + n <= ASAN_CEIL.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR Hled Hk Hn.
pose proof ASAN_CEIL_range as HC. pose proof (@cf_head_nonneg cp) as Hh.
destruct Hk as [(b & m & Hin & Hb & Hpe) | [(_ & Hlo & Hhi & _) | (Hlo & Hhi & _)]];
  try (rewrite (proj1 HPAB) in Hlo; rewrite (proj2 HPAB) in Hhi).
- pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
  destruct (Hall _ Hin) as (Hk0 & HB & _). cbn [fst snd] in Hk0, HB.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HB) as (_ & H4096 & Hceil & _).
  assert (Hmz : 0 <= m + cf_head) by (clear - Hk0 Hh; lia). pose proof (req_size_pos _ Hmz) as Rq.
  unfold ASAN_CEIL in *. clear - Rq H4096 Hceil Hb Hpe Hh HC Hn. lia.
- unfold IMG_LO, IMG_TOP, ASAN_CEIL in *. clear - Hlo Hhi HC Hn. lia.
- unfold IMG_LO, IMG_TOP, ASAN_CEIL in *. clear - Hlo Hhi HC Hn. lia.
Qed.
(* the string is outside the writer's footprint at a state whose struct lies above it *)
Lemma str_notin_fp : forall ly S Hp W mem md Lam peak cnt fail ran {most own : Z} o buf cap p n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> kept_at B Lam p n -> 0 < n ->
  (cap = 0 \/ p + n <= buf \/ buf + cap <= p) -> (cap <> 0 -> In (buf, cap) Lam) -> p + n <= o ->
  forall a, p <= a < p + n -> ~ inFP (prhWriter_cfp o buf cap) a.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own o buf cap p n HAR Hled Hk Hn Hd Hbuf Ho a Ha.
apply notin_cfp; [lia|]. intros Hc0 Hab.
pose proof (@cf_head_nonneg cp) as Hh. specialize (Hbuf Hc0).
pose proof (ps_led_nodup _ _ _ _ _ _ _ _ _ _ Hled) as Hnd. pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
destruct (Hall _ Hbuf) as (Hk0 & HB & _). cbn [fst snd] in Hk0, HB.
destruct Hk as [(b & m & Hin & Hb & Hpe) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]].
- destruct (Z.eq_dec b buf) as [-> | Hne].
  + assert (Em : m = cap).
    { clear - Hnd Hin Hbuf. induction Lam as [|[x y] t IH]; [destruct Hin|].
      cbn [map fst] in Hnd. inversion Hnd as [|x0 l0 Hn1 Hnd1].
      destruct Hin as [Heq | Hin]; destruct Hbuf as [Heq' | Hbuf].
      - congruence.
      - exfalso. apply Hn1. injection Heq as E1 E2. subst x. pose proof (in_map fst t (buf, cap) Hbuf) as Hx.
        cbn [fst] in Hx. first [ exact Hx | apply list_elem_of_In; exact Hx | apply elem_of_list_In; exact Hx ].
      - exfalso. apply Hn1. injection Heq' as E1 E2. subst x. pose proof (in_map fst t (buf, m) Hin) as Hx.
        cbn [fst] in Hx. first [ exact Hx | apply list_elem_of_In; exact Hx | apply elem_of_list_In; exact Hx ].
      - apply IH; assumption. }
    subst m. clear - Hb Hpe Hd Hc0 Hn. lia.
  + pose proof (ledger_blocks_disj ly S Hp W mem md Lam peak cnt fail ran b m buf cap HAR Hled Hin Hbuf Hne) as Hdj.
    revert Hab. unfold req_size. destruct (Z.eqb_spec (cap + cf_head) 0); intros Hab;
      clear - Hdj Hab Ha Hb Hpe Hh Hk0 Hc0; lia.
- destruct (Hro a Ha) as (Hr & _).
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HAR
    (or_introl (ex_intro _ (buf - cf_head) (ex_intro _ (cap + cf_head) (conj HB Hab)))))).
  exact (in_roP_img a Hr).
- destruct (Hro a Ha) as (Hr & _).
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HAR
    (or_introl (ex_intro _ (buf - cf_head) (ex_intro _ (cap + cf_head) (conj HB Hab)))))).
  exact (in_roP_img a Hr).
Qed.
(* the string's home, kept by a blocks arm *)
Lemma kept_at_blk : forall ly S Lam peak buf st ly' S' Lam' peak' buf' st' p n,
  prhWriter_blk B ly S Lam peak buf st ly' S' Lam' peak' buf' st' -> 0 < n ->
  (WriterApp.w_cap st = 0 \/ p + n <= buf \/ buf + WriterApp.w_cap st <= p) ->
  kept_at B Lam p n -> kept_at B Lam' p n.
Proof.
intros ly S Lam peak buf st ly' S' Lam' peak' buf' st' p n Hblk Hn Hd [(b & m & Hin & Hb & Hp) | H].
- left. exists b, m. split; [exact (blk_kept_at _ _ _ _ _ _ _ _ _ _ _ _ p n Hblk Hn Hd b m Hin Hb Hp) | lia].
- right. exact H.
Qed.
(* a string's home is application or image memory, apart from every live fake frame *)
Lemma kept_at_loc : forall ly S Hp W mem md Lam peak cnt fail ran {most own : Z} p n cid pos,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> kept_at B Lam p n -> 0 < n ->
  In (cid, pos) (frames S) -> 0 < fs_frame_bytes cid ->
  (p + n <= kLowShadowBeg \/ kHighMemBeg <= p) /\
  (p + n <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= p).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n cid pos HAR Hled Hk Hn Hfr Hfb.
pose proof (@cf_head_nonneg cp) as Hh.
destruct Hk as [(b & m & Hin & Hb & Hpe) | [(_ & Hlo & Hhi & Hall) | (Hlo & Hhi & Hall)]];
  try (rewrite (proj1 HPAB) in Hlo; rewrite (proj2 HPAB) in Hhi).
- pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
  destruct (Hall _ Hin) as (Hk0 & HB & _). cbn [fst snd] in Hk0, HB.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HB) as (_ & H4096 & Hceil & Happ & _).
  assert (Hmz : 0 <= m + cf_head) by (clear - Hk0 Hh; lia). pose proof (req_size_pos _ Hmz) as Rq.
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR HB Hfr) as Hzd.
  unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. unfold in_app in Happ.
  split; [clear - Happ Rq Hb Hpe Hh Hn; lia | clear - Hzd Rq Hb Hpe Hh Hn; lia].
- split; [unfold IMG_TOP, kLowShadowBeg in *; clear - Hhi Hn; lia|].
  destruct (Z_le_gt_dec (p + n) (frame_addr ly cid pos)) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (frame_addr ly cid pos + fs_frame_bytes cid) p) as [H2 | H2]; [right; exact H2|]. exfalso.
  assert (Hmx : p <= Z.max p (frame_addr ly cid pos) < p + n) by (clear - H1 H2 Hn; lia).
  assert (Hmf : frame_addr ly cid pos <= Z.max p (frame_addr ly cid pos) < frame_addr ly cid pos + fs_frame_bytes cid)
    by (clear - H1 H2 Hn Hfb; lia).
  destruct (Hall _ Hmx) as (Hro & _).
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md _ HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hfr Hmf))))))).
  exact (in_roP_img _ Hro).
- split; [unfold IMG_TOP, kLowShadowBeg in *; clear - Hhi Hn; lia|].
  destruct (Z_le_gt_dec (p + n) (frame_addr ly cid pos)) as [H1 | H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (frame_addr ly cid pos + fs_frame_bytes cid) p) as [H2 | H2]; [right; exact H2|]. exfalso.
  assert (Hmx : p <= Z.max p (frame_addr ly cid pos) < p + n) by (clear - H1 H2 Hn; lia).
  assert (Hmf : frame_addr ly cid pos <= Z.max p (frame_addr ly cid pos) < frame_addr ly cid pos + fs_frame_bytes cid)
    by (clear - H1 H2 Hn Hfb; lia).
  destruct (Hall _ Hmx) as (Hro & _).
  apply (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md _ HAR
    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hfr Hmf))))))).
  exact (in_roP_img _ Hro).
Qed.
(* one byte read through the view *)
Lemma val_mem1_of_aview : forall H (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
destruct (aview_byte SEGS H mem _ _ Hv) as (b & Hb & -> & Hr).
replace (a + Z.of_nat 0) with a by lia. rewrite Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8)) by (clear - Hr; lia).
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* pairwise of a symmetric relation is kept by a permutation *)
Lemma pw_perm : forall {X} (R : X -> X -> Prop) l l', (forall a b, R a b -> R b a) ->
  Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R l l' Hs Hp. induction Hp as [| x l l' Hp IH | x y l | l l' l'' H1 IH1 H2 IH2]; cbn [pairwise].
- tauto.
- intros (Hf & Hpl). split; [|exact (IH Hpl)]. rewrite Forall_forall in *. intros z Hz.
  apply Hf. exact (Permutation_in z (Permutation_sym Hp) Hz).
- intros (Hf1 & Hf2 & Hpl). inversion Hf1 as [|y0 l0 Hyx Hfl]. subst.
  split; [constructor; [exact (Hs _ _ Hyx) | exact Hf2]|]. split; [exact Hfl | exact Hpl].
- intros H. exact (IH2 (IH1 H)).
Qed.
(* ---- the put step: one put call from a join state, generic in the piece ---- *)
(* the realigned frame of a 16-aligned sp *)
Lemma ps_R_facts : forall sp, sp mod 16 = 0 -> sp - 208 <= PS_R sp <= sp - 192 /\ PS_R sp mod 32 = 0.
Proof.
intros sp Hal. unfold PS_R. pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)).
assert ((sp - 192) mod 32 = 0 \/ (sp - 192) mod 32 = 16).
{ pose proof (Z.div_mod sp 16 ltac:(lia)). pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)). lia. }
split; [lia|]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.
(* a word whose eight bytes are visible reads *)
Lemma rdword_some_of : forall (v : reader) a, (forall i, 0 <= i < 8 -> v (a + i) <> None) -> exists w, rdword v a = Some w.
Proof.
intros v a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2.
pose proof (H 3 ltac:(lia)) as H3. pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5.
pose proof (H 6 ltac:(lia)) as H6. pose proof (H 7 ltac:(lia)) as H7. rewrite Z.add_0_r in H0.
destruct (v a); [|congruence]. destruct (v (a + 1)); [|congruence]. destruct (v (a + 2)); [|congruence].
destruct (v (a + 3)); [|congruence]. destruct (v (a + 4)); [|congruence]. destruct (v (a + 5)); [|congruence].
destruct (v (a + 6)); [|congruence]. destruct (v (a + 7)); [|congruence]. eexists. reflexivity.
Qed.
(* a word read through two views that agree on its eight bytes *)
Lemma rdword_eq_of : forall (v v' : reader) a,
  (forall i, 0 <= i < 8 -> v' (a + i) = v (a + i)) -> rdword v' a = rdword v a.
Proof.
intros v v' a H. unfold rdword.
rewrite <- (Z.add_0_r a) at 1 2. rewrite !H by lia. rewrite Z.add_0_r. reflexivity.
Qed.
(* the entry footprint is closed (positive starts) *)
Lemma ps_fp_closed : forall X ch, ps_pre X ch -> ~ YI16.sink_open_fp (x_FP X).
Proof.
intros X ch Hpre.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & _ & Ho1 & _ & Hout0 & Hled0 & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
apply sink_closed_pos. unfold x_FP, prhWriter_cfp, prhWriter_fp.
destruct (Z.eqb_spec (WriterApp.w_cap (x_st X)) 0) as [Hz0 | Hnz]; constructor; cbn [fst];
  try (unfold x_sp in Ho1; clear - Ho1 Hceil HC Hstk0 Hslo; lia).
- cbn. constructor.
- cbn -[ablocks_fp]. unfold ablocks_fp. cbn [map]. constructor; [cbn [fst] | constructor].
  destruct Hout0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & HinL & _)]); [lia|].
  pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled0) as Hall. rewrite Forall_forall in Hall.
  destruct (Hall _ HinL) as (_ & HB & _). cbn [fst snd] in HB.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HB) as (_ & H4096 & _). clear - H4096; lia.
Qed.

(* a byte above sp, of the image or of a live block is apart from the walk's own frame [R, sp), the fake frame and the
   shadow band (the walk's journal at any world relation R) *)
Lemma ps_out_ownR : forall (R : world SEGS -> world SEGS -> Prop) X ch pos lyc Sc Hpc Wc memc mdc kc a,
  ps_pre X ch ->
  AJR R (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc mdc kc ->
  (x_sp X <= a < 2 ^ 64 \/ in_img SEGS a \/ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) ->
  (a < x_R X \/ x_sp X <= a) /\ (a < x_F X pos \/ x_F X pos + 64 <= a) /\ (a < SHADOW_OFF \/ kHighMemBeg <= a).
Proof.
intros R X ch pos lyc Sc Hpc Wc memc mdc kc a Hpre HJ Ha.
pose proof Hpre as (HFPRE & _). destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HARc) as (_ & HFb).
rewrite Forall_forall in HFb. destruct (HFb (0, pos) HinF) as (HF4096 & HFceil). cbn [fst snd] in HF4096, HFceil.
assert (EF : frame_addr lyc 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
rewrite EF in HF4096, HFceil. change (fs_frame_bytes 0) with 64 in HFceil.
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
unfold x_R. unfold x_sp in *.
destruct Ha as [Ha | [Hi | (b & m & HB & Hb)]].
- unfold SHADOW_OFF, kHighMemBeg in *. clear - Ha HR HFceil HC Hceil Hslo Hstk0 HSTK208. lia.
- pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  split; [left; clear - Hl HR HC Hceil Hslo Hstk0 HSTK208; lia|].
  split; [|left; unfold SHADOW_OFF; clear - Hl; lia].
  destruct (Z_lt_le_dec a (x_F X pos)) as [H1 | H1]; [left; exact H1|].
  destruct (Z_lt_le_dec a (x_F X pos + 64)) as [H2 | H2]; [exfalso | right; exact H2].
  assert (Hmf : frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + fs_frame_bytes 0)
    by (rewrite EF; change (fs_frame_bytes 0) with 64; clear - H1 H2; lia).
  apply (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ a HARc
    (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj HinF Hmf))))))). exact Hi.
- destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc HB) as (_ & Hb4096 & Hbceil & Hbapp & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HARc HB HinF) as Hzd.
  unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite EF in Hzd. change (fs_frame_bytes 0) with 64 in Hzd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  clear - Hb Hbceil Hbapp Hzd HR HC Hceil Hslo Hstk0 HSTK208. lia.
Qed.
(* ps_out_ownR at wle *)
Lemma ps_out_own : forall X ch pos lyc Sc Hpc Wc memc mdc kc a,
  ps_pre X ch ->
  AJ (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc mdc kc ->
  (x_sp X <= a < 2 ^ 64 \/ in_img SEGS a \/ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) ->
  (a < x_R X \/ x_sp X <= a) /\ (a < x_F X pos \/ x_F X pos + 64 <= a) /\ (a < SHADOW_OFF \/ kHighMemBeg <= a).
Proof. exact (ps_out_ownR (@wle SEGS)). Qed.

(* the join invariant across a stretch of the walk's own code: the journal and Pm at the end, the saved slots and the
   flag-cell word re-read there, and every byte above sp, of the image or of a live block kept (at any world
   relation R of the join's journal) *)
Lemma ps_common_runR : forall (R : world SEGS -> world SEGS -> Prop) X pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc',
  ps_commonR R X pos P lyc Sc Hpc Wc memc mdc kc -> x_sp X <= x_o X -> x_o X + 32 <= 2 ^ 64 ->
  AJR R (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' -> ps_saved_ok X Wc memc' ->
  rdword (aview SEGS (w_H Wc) memc') (x_F X pos + 56) = Some (x_FL X pos) ->
  (forall a, (x_sp X <= a < 2 ^ 64 \/ in_img SEGS a \/
      exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  ps_commonR R X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof.
intros R X pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hcom Hso Hoe HJ' HPm' Hsav' HF56' K.
destruct Hcom as (_ & _ & _ & Hok & _ & (ok & ranc & bufc & Lamc & peakc & Hoks & Hout & Hled & Hblk & Hkept &
  Hlive & Hdisj & Hrp) & Hroom & Hro & Hwk & Hfl).
pose proof (ajxR_ar HJ') as HAR'.
pose proof (@cf_head_nonneg cp) as Hh.
assert (KB : forall b k a, In (b, k) Lamc -> b - cf_head <= a < b + k ->
  aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros b k a Hin Ha. apply K. right. right.
  pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
  destruct (Hall _ Hin) as (Hk0 & HB & _). cbn [fst snd] in Hk0, HB.
  exists (b - cf_head), (k + cf_head). split; [exact HB|].
  assert (Hz : 0 <= k + cf_head) by (clear - Hk0 Hh; lia). pose proof (req_size_pos _ Hz) as Rq. clear - Ha Rq. lia. }
assert (Hled' : prh_ledger B lyc Sc Hpc Wc memc' Lamc peakc (WriterApp.w_cnt (prhWriter_putN ok (x_st X) P))
  (WriterApp.w_fail (prhWriter_putN ok (x_st X) P)) ranc (x_most X) (x_own X)).
{ apply (prh_ledger_kept lyc Sc Hpc Wc memc Lamc peakc _ _ ranc lyc Sc Wc memc' Hled eq_refl).
  - intros a Ha. apply K. right. left. exact (proj1 (PST_ok a (gcell_pst a Ha))).
  - intros b k a Hin Ha. apply (KB b k a Hin). unfold prh_head_wide in HW. pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall.
    rewrite Forall_forall in Hall. destruct (Hall _ Hin) as (Hk0 & _). cbn [snd] in Hk0. clear - Ha HW Hk0. lia. }
assert (Hcase : WriterApp.w_cap (prhWriter_putN ok (x_st X) P) <> 0 ->
  In (bufc, WriterApp.w_cap (prhWriter_putN ok (x_st X) P)) Lamc).
{ intros Hc0. destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & HinL & _)]); [lia | exact HinL]. }
split; [exact HJ'|]. split; [exact Hsav'|]. split; [exact HF56'|].
split; [intros a Ha1 Ha2; rewrite K; [exact (Hok a Ha1 Ha2)|]; left; clear - Ha1 Ha2 Hoe; lia|].
split; [exact HPm'|].
split.
{ exists ok, ranc, bufc, Lamc, peakc. split; [exact Hoks|]. split.
  - apply (prhW_out_kept Wc memc Lamc (x_o X) bufc _ Wc memc' lyc Sc Hpc mdc' Hout HAR').
    + intros Hc0. pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled') as Hall. rewrite Forall_forall in Hall.
      exact (Hall _ (Hcase Hc0)).
    + intros a Ha. apply K. left. clear - Ha Hso Hoe; lia.
    + intros Hc0 a Ha. apply (KB _ _ a (Hcase Hc0)). clear - Ha Hh. lia.
  - split; [exact Hled'|]. split; [exact Hblk|]. split; [exact Hkept|]. split; [exact Hlive|].
    split; [exact Hdisj | exact Hrp]. }
split; [exact Hroom|].
split.
{ intros a Hro' Ho' He'. rewrite (K a (or_intror (or_introl (in_roP_img a Hro')))). exact (Hro a Hro' Ho' He'). }
split; [|exact Hfl].
pose proof (ajxR_stk HJ') as (_ & _ & _ & _ & Hhi & H47 & _).
intros a Ha1 Ha2. assert (Ha64 : a < 2 ^ 64) by (clear - Ha1 Hhi H47; lia).
rewrite (K a (or_introl (conj (proj1 Ha1) Ha64))).
exact (Hwk a Ha1 Ha2).
Qed.
(* ps_common_runR at wle *)
Lemma ps_common_run : forall X pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc',
  ps_common X pos P lyc Sc Hpc Wc memc mdc kc -> x_sp X <= x_o X -> x_o X + 32 <= 2 ^ 64 ->
  AJ (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' -> ps_saved_ok X Wc memc' ->
  rdword (aview SEGS (w_H Wc) memc') (x_F X pos + 56) = Some (x_FL X pos) ->
  (forall a, (x_sp X <= a < 2 ^ 64 \/ in_img SEGS a \/
      exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  ps_common X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof. exact (ps_common_runR (@wle SEGS)). Qed.

(* the join invariant across a tokenless stretch whose write windows stay in the walk's own areas: the realigned
   slots [R, R + 88), the fake frame's first 56 bytes (header, u) and the shadow band; the saved slots, the flag-cell
   word F + 56 and every byte above sp, of the image or of a live block are outside them, so frame_of keeps them (at
   any world relation R of the join's journal) *)
Lemma ps_common_frameR : forall (R : world SEGS -> world SEGS -> Prop) X ch pos P lyc Sc Hpc Wc memc mdc kc E rs memc'
    mdc' kc',
  ps_pre X ch -> ps_commonR R X pos P lyc Sc Hpc Wc memc mdc kc ->
  AJR R (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  frame_of E rs (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  (forall a, in_wrange E rs a ->
     x_R X <= a < x_R X + 88 \/ x_F X pos <= a < x_F X pos + 56 \/ SHADOW_OFF <= a < kHighMemBeg) ->
  ps_commonR R X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof.
intros R X ch pos P lyc Sc Hpc Wc memc mdc kc E rs memc' mdc' kc' Hpre Hcom HJ' HPm' Hfr Hwr.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HWIN0 & Ho1 & Ho2 & _).
destruct HFPRE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & _ & Hdtop & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
pose proof (ajxR_ar HJ') as HARc. pose proof (ajxR_ly HJ') as HLLE. pose proof (ajxR_frs HJ') as HFRS.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HARc) as (_ & HFb).
rewrite Forall_forall in HFb. destruct (HFb (0, pos) HinF) as (HF4096 & HFceil). cbn [fst snd] in HF4096, HFceil.
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HARc HinF) as (_ & (HFa0 & HFa1) & _ & _).
assert (EF : frame_addr lyc 0 pos = x_F X pos) by (unfold x_F, frame_addr; rewrite HlyF; reflexivity).
rewrite EF in HF4096, HFceil, HFa0, HFa1. change (fs_frame_bytes 0) with 64 in HFceil, HFa0, HFa1.
assert (KK : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_R X <= a < x_R X + 88 \/ x_F X pos <= a < x_F X pos + 56 \/ SHADOW_OFF <= a < kHighMemBeg) ->
  aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply (kept_of_frame E rs (w_H Wc) memc memc' (fun x => x = a) Hfr); [|reflexivity].
  intros x ->. split; [exact Ha|]. intros Hw. exact (Hn (Hwr a Hw)). }
pose proof Hcom as (_ & Hsav & HF56 & _).
unfold x_R in *. unfold x_sp in *. set (F := x_F X pos) in *.
apply (ps_common_runR R X pos P lyc Sc Hpc Wc memc mdc kc memc' mdc' kc' Hcom).
- exact Ho1.
- clear - Ho2 Hdtop Htop2 H47. lia.
- exact HJ'.
- exact HPm'.
- unfold ps_saved_ok in Hsav |- *. unfold x_sp in Hsav |- *. rewrite Forall_forall in Hsav |- *.
  intros pz Hpin. rewrite <- (Hsav pz Hpin). apply rdword_eq_of. intros i Hi.
  assert (Hrg : -104 <= fst pz <= -8).
  { unfold ps_saved_list in Hpin. cbn [In] in Hpin. repeat (destruct Hpin as [<- | Hpin]; [cbn [fst]; lia|]). destruct Hpin. }
  apply KK.
  + clear - Hrg Hi HC Hceil Hslo Hstk0 HSTK208 Hshi H47. lia.
  + unfold SHADOW_OFF, kHighMemBeg in *. clear - Hrg Hi HR HFceil HC Hceil Hslo Hstk0 HSTK208. lia.
- rewrite <- HF56. apply rdword_eq_of. intros i Hi. apply KK.
  + clear - Hi HF4096 HFceil HC. lia.
  + unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. clear - Hi HR HFceil HFa1 HC Hceil Hslo Hstk0 HSTK208. lia.
- intros a Ha. destruct (ps_out_ownR R X ch pos lyc Sc Hpc Wc memc' mdc' kc' a Hpre HJ' Ha) as (O1 & O2 & O3).
  unfold x_R, x_sp in O1. fold F in O2. apply KK.
  + destruct Ha as [Ha | [Hi | (b & m & HB & Hb)]].
    * unfold x_sp in Ha. clear - Ha HC Hceil Hslo Hstk0 HSTK208. lia.
    * pose proof (segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. clear - Hl. lia.
    * destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc HB) as (_ & Hb4096 & Hbceil & _).
      unfold ASAN_CEIL in Hbceil. clear - Hb Hb4096 Hbceil HC. lia.
  + clear - O1 O2 O3 HR. lia.
Qed.
(* ps_common_frameR at wle *)
Lemma ps_common_frame : forall X ch pos P lyc Sc Hpc Wc memc mdc kc E rs memc' mdc' kc',
  ps_pre X ch -> ps_common X pos P lyc Sc Hpc Wc memc mdc kc ->
  AJ (STK_put_string + x_d X) (x_sp X + x_d X) (x_FP X) (x_ly X) (x_S X) (x_Hp X) (x_W X) (x_mem X) (x_md X)
     [(0, pos)] lyc Sc Hpc Wc memc' mdc' kc' ->
  Pm memc' ->
  frame_of E rs (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  (forall a, in_wrange E rs a ->
     x_R X <= a < x_R X + 88 \/ x_F X pos <= a < x_F X pos + 56 \/ SHADOW_OFF <= a < kHighMemBeg) ->
  ps_common X pos P lyc Sc Hpc Wc memc' mdc' kc'.
Proof. exact (ps_common_frameR (@wle SEGS)). Qed.

(* the frame chain at a call view of the walk (callee sp = R): put_string's own record (sp, ra, s0) on the chain from
   the caller's s0, which the named argument ps_s0 makes at most one record (s0 = o: the record at o, form (a) of the
   text; s0 below the ceiling: none) *)
Definition ps_s0 (X : psx) : Prop := s0Z (x_regs X) = x_o X \/ s0Z (x_regs X) < YM05.alloc_ceiling.
Lemma ps_call_chain : forall X ch lyc (Wc : world SEGS) memc,
  ps_pre X ch -> ps_s0 X -> ly_top lyc = ly_top (x_ly X) ->
  ps_saved_ok X Wc memc -> ps_okeep X Wc memc ->
  exists ch1, achain lyc (aview SEGS (w_H Wc) memc) (x_R X) (x_sp X) ch1.
Proof.
intros X ch lyc Wc memc Hpre HS0 HlyT Hsav Hok.
pose proof Hpre as (HFPRE & _ & _ & _ & _ & _ & Hocase & Hoch & HWIN0 & Ho1 & Ho2 & Hout0 & _).
destruct HFPRE as (HPRE & _ & Htopstk & Hraceil & _).
pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN0 as (Hd0 & _ & Hdtop & _).
pose proof (proj1 Hout0) as Ho8.
destruct (ps_R_facts (x_sp X) Hal16) as (HR & _).
unfold ps_saved_ok in Hsav. rewrite Forall_forall in Hsav.
pose proof (Hsav (-8, 1) ltac:(unfold ps_saved_list; cbn [In]; tauto)) as Hs8. cbn [fst snd] in Hs8.
pose proof (Hsav (-16, 8) ltac:(unfold ps_saved_list; cbn [In]; tauto)) as Hs16. cbn [fst snd] in Hs16.
unfold ps_okeep in Hok. unfold x_R. unfold x_sp in *.
set (sp := spZ (x_regs X)) in *.
(* the chain from s0 at the call view *)
assert (Hc0 : exists ch', achain lyc (aview SEGS (w_H Wc) memc) sp (s0Z (x_regs X)) ch').
{ destruct HS0 as [E0 | L0]; [|exists []; apply achain_low; exact L0].
  rewrite E0 in Hch |- *.
  destruct Hch as [([Hl | [Hl | Hl]] & _) | (Hv16 & Hvt & Hv8 & Hfp & _)].
  - exists []. apply achain_low. exact Hl.
  - exfalso. clear - Hl Ho2 Hdtop Ho1. unfold sp in *. lia.
  - exfalso. apply Hl. exact Ho8.
  - destruct (Hoch Hv16) as (ra8 & Hra8 & nfp & Hn16 & Hnc).
    destruct ch as [|[[fp ra] nf] rest].
    { exists []. right. split; [exact Hv16|]. split; [rewrite HlyT; exact Hvt|]. split; [exact Hv8|].
      split; [|constructor]. cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr4096). exists r.
      split; [|exact Hr4096]. rewrite <- Hr. apply rdword_eq_of. intros i Hi. apply Hok; clear - Hi Hv16; lia. }
    cbn [fpchain] in Hfp. destruct Hfp as (-> & Hal & Hl8 & Hl16 & Hra & _).
    rewrite Hl8 in Hra8. injection Hra8 as <-. rewrite Hl16 in Hn16. injection Hn16 as <-.
    exists [(x_o X, ra, nf)]. right. split; [exact Hv16|]. split; [rewrite HlyT; exact Hvt|]. split; [exact Hv8|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|].
      split; [rewrite <- Hl8; apply rdword_eq_of; intros i Hi; apply Hok; clear - Hi Hv16; lia|].
      split; [rewrite <- Hl16; apply rdword_eq_of; intros i Hi; apply Hok; clear - Hi Hv16; lia|].
      split; [exact Hra|].
      assert (Hb : bad_next (x_o X) (ly_top lyc) nf = true).
      { unfold bad_next. apply Bool.orb_true_intro. left. apply Bool.orb_true_intro. left. apply Z.leb_le.
        clear - Hnc Ho1 Hceil Hslo Hstk0. unfold sp in *. lia. }
      rewrite Hb. reflexivity.
    + constructor; [cbn [fst]; exact Hv16 | constructor]. }
destruct Hc0 as (ch' & Hc0).
exists ((sp, bv_unsigned (getr (x_regs X) (Z_to_bv 5 1)), s0Z (x_regs X)) :: ch').
apply (achain_push lyc (aview SEGS (w_H Wc) memc) (aview SEGS (w_H Wc) memc) sp (s0Z (x_regs X))
  (bv_unsigned (getr (x_regs X) (Z_to_bv 5 1))) ch' (PS_R sp) Hc0).
- rewrite HlyT. clear - Htop2 H47. lia.
- intros a _. reflexivity.
- replace (sp - 8) with (sp + -8) by (clear; lia). exact Hs8.
- replace (sp - 16) with (sp + -16) by (clear; lia). exact Hs16.
- exact Hra4.
- clear - Hceil Hslo Hstk0. lia.
- clear - Hal16. lia.
- rewrite HlyT. clear - Ho1 Ho2 Hdtop. lia.
- clear - HR. lia.
Qed.

(* the put call step: put's own run reallocs its buffer when it grows (a crossing call), so the join before the call,
   the join after it and the conclusion are at the re-hiding relation wle' SEGS RZ_cf; a caller at the first put lifts
   its join at wle by ps_commonR_mono with wle_wle' *)
Lemma ps_put_step : forall X ch pos P b rest lyc Sc Hpc Wc regsc memc mdc kc raw sb (Q : world SEGS -> config -> Prop),
  ps_pre X ch -> ps_s0 X ->
  ps_commonR (wle' SEGS RZ_cf) X pos P lyc Sc Hpc Wc memc mdc kc ->
  WriterSpec.spieces (x_bs X) = P ++ b :: rest ->
  spZ regsc = x_R X -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  s0Z regsc = x_sp X ->
  getr regsc 10 = w64 (x_o X) -> getr regsc 11 = w64 sb -> getr regsc 12 = w64 (Z.of_nat (length b)) ->
  src_rd Wc memc sb b ->
  (forall Lamc bufc capc, kept_at B Lamc (x_s X) (x_n X + 1) ->
     (capc = 0 \/ x_s X + x_n X + 1 <= bufc \/ bufc + capc <= x_s X) ->
     (capc <> 0 -> In (bufc, capc) Lamc) ->
     (forall b0 m, In (b0, m) Lamc -> In (b0 - cf_head, m + cf_head) (ablocks B lyc Sc)) ->
     prhWriter_src_home B lyc Sc Lamc bufc capc sb (Z.of_nat (length b))) ->
  (forall ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     ps_commonR (wle' SEGS RZ_cf) X pos (P ++ [b]) ly2 S2 Hp2 W2 mem2 md2 (kc + k1) ->
     aregs_preserved regsc regs2 ->
     (forall a, x_R X <= a < x_sp X -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
     (forall a, x_R X <= a < x_sp X -> apresent (w_H W2) mem2 a) ->
     (forall a, (x_F X pos <= a < x_F X pos + 64 \/ x_SHF X pos <= a < x_SHF X pos + 8) ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a) ->
     SRr' SEGS RZ_cf W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr' SEGS RZ_cf Wc (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros X ch pos P b rest lyc Sc Hpc Wc regsc memc mdc kc raw sb Q Hpre HS0 Hcom Hplan Hsp Hgp Htp Hra Hraw Hra4
  Hrac Hs0c H10 H11 H12 Hsrc Hhome K.
pose proof (ps_fp_closed X ch Hpre) as Hcl0.
pose proof Hpre as (HFPRE & Hroom0 & Hrp0 & Huniv & H10e & H11e & Hocase & Hoch & HWIN0 & Ho1 & Ho2 & Hout0 & Hled0 &
  Hcstr0 & Hkept0 & Hdisj0 & Hfr & Hwmax0 & Hhead & Hlive0 & Hcons0 & Hevs0 & Hlen4).
destruct HFPRE as (HPRE & Hro0 & Htopstk & Hraceil & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & _).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & _).
pose proof ASAN_CEIL_range as HC. unfold ASAN_CEIL in HC.
destruct Hcom as (HJ & Hsav & HF56 & Hok & HPm & (ok & ranc & bufc & Lamc & peakc & (Hoks & G1) & Hout & Hled & Hblk &
  Hkept & Hlive & Hdisj & (rph1 & Hrp1)) & Hroom & Hro & Hwk0 & Hfl).
pose proof Hfl as (Hfz & _).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as HLLE. pose proof (ajxR_frs HJ) as HFRS.
pose proof HLLE as (_ & _ & _ & _ & _ & HlyF & _ & _ & HlyT & _ & HlyH & _).
destruct (ps_call_chain X ch lyc Wc memc Hpre HS0 HlyT Hsav Hok) as (ch1 & Hch1).
rewrite <- Hs0c in Hch1.
destruct X as [d ly S Hp W regs mem md o s bs buf st Lam peak ran rpsm rpx rpos rpi rpH0 rphist most own fx0].
cbn [x_d x_ly x_S x_Hp x_W x_regs x_mem x_md x_o x_s x_bs x_buf x_st x_Lam x_peak x_ran x_rpsm x_rpx x_rpos x_rpi
  x_rpH0 x_rphist x_most x_own x_fx] in *.
unfold x_R, x_n, x_SHF, x_FL, x_F, x_FP in *. unfold x_sp in *. cbn [x_regs x_bs x_ly x_o x_buf x_st] in *.
set (sp := spZ regs) in *. set (R := PS_R sp) in *.
destruct (ps_R_facts sp Hal16) as (HR & HR32).
set (st1 := prhWriter_putN ok st P) in *.
(* put's run event, read off the kit's entry premise at the EXACT position the walk holds (S7a's prhWriter_ev_at) *)
assert (HEVc : prhWriter_grows st1 b = true -> WriterApp.w_cnt st1 <> WriterApp.w_fail st1 ->
  nth_error (PresetRun.hruns rpsm rpx rpos) (rpi + length (prhWriter_evs ok st P))%nat = Some (prhWriter_ev st1 b)).
{ intros Hgr Hcr. rewrite Hplan in Hevs0.
  exact (prhWriter_ev_at rpsm rpx rpos rpi _ st P b rest ok Hevs0 eq_refl Hgr Hcr). }
set (FPc := prhWriter_cfp o bufc (WriterApp.w_cap st1)).
assert (Hcase : WriterApp.w_cap st1 <> 0 -> In (bufc, WriterApp.w_cap st1) Lamc).
{ intros Hc0. destruct Hout as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & HinL & _)]); [lia | exact HinL]. }
assert (Hcap0 : 0 <= WriterApp.w_cap st) by (destruct Hout0 as (_ & _ & Hc & _); lia).
assert (Hcnt0 : 0 <= WriterApp.w_cnt st) by (pose proof (ps_led_cnt _ _ _ _ _ _ _ _ _ _ Hled0) as Hc; lia).
(* the plan's lengths *)
assert (HcatP : (length (concat P) + length b <= length (WriterSpec.wstr bs))%nat).
{ unfold WriterSpec.wstr. rewrite Hplan, concat_app, length_app. cbn [concat]. rewrite length_app. lia. }
pose proof (prhWriter_putN_len_le ok st P) as HlenN. fold st1 in HlenN.
assert (HW1 : Z.of_nat (length (WriterApp.w_text st1)) + Z.of_nat (length b) + 1 <= prhWriter_WMAX) by lia.
assert (HW2 : Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (P ++ [b]))) + 1 <= prhWriter_WMAX).
{ rewrite concat_app. cbn [concat]. rewrite app_nil_r, length_app. lia. }
(* put's live room and consumer window (the batch kit's PRH_FnWriter.v d89d3c67b78c :471 / :421) from put_string's (:636 / :584):
   S7a_WriterRet's one copy (prhWriter_live_evs_at / prhWriter_cons_at, WalkS7aR 8c237bd1fbb4) *)
pose proof (prhWriter_blk_bb B _ _ _ _ _ _ _ _ _ _ _ _ Hcap0 Hblk) as Hbb.
rewrite Hplan in Hlive0, Hcons0.
assert (HROOM : prh_live_evs Sc (prhWriter_evs [] st1 [b]) /\
  PRH_Base.prh_cons_from rpsm rpx rpos (rpi + length (prhWriter_evs ok st P)) (length (prhWriter_evs [] st1 [b]))).
{ split.
  - first [ exact (prhWriter_live_evs_at S Sc st P b rest ok Hcap0 Hlive0 Hbb)
          | exact (prhWriter_live_evs_at B S Sc st P b rest ok Hcap0 Hlive0 Hbb) ].
  - exact (prhWriter_cons_at rpsm rpx rpos rpi st P b rest ok Hcons0). }
(* the footprint of the call is inside the walk's *)
assert (HFPS : fp_sub_x B (STK_put_string + d) (sp + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) FPc ly S
  [(0, pos)] lyc Sc).
{ assert (HSTKp : 0 <= STK_put_string) by (vm_compute; congruence).
  intros a (r & Hr & Ha). unfold FPc, prhWriter_cfp in Hr. cbn [In] in Hr.
  destruct Hr as [<- | Hr]; [right; right; right; cbn [fst snd] in Ha; clear - Ha Ho1 Ho2 HR Hd0 HSTKp; lia|].
  destruct Hblk as [(Ec & Eb & _ & _ & _) | (Lt & l1 & l2 & b1 & b2 & Hc & EL & _ & Hperm)].
  - left. exists r. split; [|exact Ha]. unfold prhWriter_cfp. right. fold st1 in Ec. rewrite <- Ec, <- Eb. exact Hr.
  - unfold prhWriter_fp in Hr. revert Hr.
    destruct (Z.eqb_spec (WriterApp.w_cap st1) 0) as [Hz | Hnz]; intros Hr; [destruct Hr|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p0 n0] & Er & Hin0). cbn [In] in Hin0.
    destruct Hin0 as [Heq0 | []]. injection Heq0 as Ep0 En0. subst p0 n0 r. cbn [fst snd] in Ha.
    right. left. exists (bufc - cf_head), (WriterApp.w_cap st1 + cf_head).
    split; [|split; [|clear - Ha; lia]].
    + pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
      destruct (Hall _ (Hcase Hnz)) as (_ & HB & _). exact HB.
    + intros HinS. pose proof (@cf_head_nonneg cp) as Hh.
      destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HARc) as (Hpw & _).
      destruct (pairwise_app_l _ _ _ Hpw) as (Hpw1 & _).
      set (f := fun b0 : Z * Z => (fst b0, req_size (snd b0))) in *.
      pose proof (pw_perm zdisjoint _ _ ltac:(intros x y Hxy; unfold zdisjoint in *; lia) (Permutation_map f Hperm) Hpw1)
        as Hpw2.
      cbn [map] in Hpw2. destruct Hpw2 as (Hf & _). rewrite Forall_forall in Hf.
      assert (Hin12 : In (bufc - cf_head, WriterApp.w_cap st1 + cf_head) (b1 ++ b2)).
      { destruct Hc as [(Z0 & -> & -> & -> & ->) | (NZ & ELam & EA)]; [exact HinS|].
        rewrite EA in HinS. apply in_app_or in HinS. apply in_or_app.
        destruct HinS as [H | [Heq | H]]; [left; exact H | | right; exact H].
        injection Heq as _ Ec. clear - Ec Lt. lia. }
      pose proof (Hf _ (in_map f _ _ Hin12)) as Hz. unfold f, zdisjoint in Hz. cbn [fst snd] in Hz.
      assert (Hcz : 0 <= WriterApp.w_cap st1 + cf_head) by (clear - Lt Hcap0 Hh; lia).
      pose proof (req_size_pos _ Hcz) as Rq. clear - Hz Rq. lia. }
idtac "PSTEP-FPS".
(* the chain from o at the call view *)
assert (Hcho : exists ra, rdword (aview SEGS (w_H Wc) memc) (o - 8) = Some ra /\
  exists nfp, rdword (aview SEGS (w_H Wc) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
{ unfold ps_okeep in Hok. cbn [x_o x_sp x_W x_mem x_regs] in Hok. unfold x_sp in Hok. cbn [x_regs] in Hok.
  fold sp in Hok.
  destruct Hocase as [Hc1 | Hc2].
  - destruct (Hoch Hc1) as (ra & Hra8 & nfp & Hn16 & Hnc). exists ra. split.
    + rewrite <- Hra8. apply rdword_eq_of. intros i Hi. apply Hok; clear - Hi Hc1; lia.
    + exists nfp. split; [|exact Hnc]. rewrite <- Hn16. apply rdword_eq_of. intros i Hi. apply Hok; clear - Hi Hc1; lia.
  - (* o = sp + 8: the word at sp is the caller's, kept; the word at sp - 8 is this function's own saved ra *)
    assert (Hpr : forall i, 0 <= i < 8 -> aview SEGS (w_H Wc) memc (o - 8 + i) <> None).
    { intros i Hi. rewrite Hok by (clear - Hi Hc2; lia).
      apply (aview_some_of_apresent SEGS). destruct HWIN0 as (_ & _ & _ & Hpres0). apply Hpres0.
      clear - Hi Hc2 Ho2; lia. }
    destruct (rdword_some_of _ _ Hpr) as (ra & Hra8). exists ra. split; [exact Hra8|].
    unfold ps_saved_ok in Hsav. cbn [x_sp x_regs] in Hsav. unfold x_sp in Hsav. cbn [x_regs] in Hsav. fold sp in Hsav.
    rewrite Forall_forall in Hsav. pose proof (Hsav (-8, 1) ltac:(unfold ps_saved_list; cbn [In]; tauto)) as Hs8.
    cbn [fst snd] in Hs8. exists (bv_unsigned (getr regs (Z_to_bv 5 1))).
    replace (o - 16) with (sp + -8) by (clear - Hc2; lia). split; [exact Hs8|]. exact Hraceil. }
(* the call *)
unfold SRr'. eapply (SRrG_bind SEGS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
{ apply (ps_put_call (most := most) (gown := own) rpsm rpx rpos (rpi + length (prhWriter_evs ok st P))%nat rpH0 rph1
    (STK_put_string + d) (sp + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [(0, pos)] lyc Sc Hpc Wc memc mdc kc regsc raw ch1
    o sb (Z.of_nat (length b)) bufc st1 b Lamc peakc ranc (R - (sp + d))).
  - exact HJ.
  - rewrite Hsp. clear; lia.
  - rewrite Zminus_mod, Zplus_mod, Hal16, Hd16. pose proof HR32 as H32.
    assert (H16 : R mod 16 = 0) by (clear - H32; lia). rewrite H16. reflexivity.
  - clear - HR Hd0; lia.
  - pose proof STK_ps_facts as (_ & _ & H0 & _). exact H0.
  - pose proof STK_ps_facts as (_ & SK2 & _). clear - SK2 HR Hd0; lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - exact Hrac.
  - replace (sp + d + (R - (sp + d))) with R by (clear; lia). exact Hch1.
  - exact Hro.
  - rewrite HlyH. clear - Htopstk HR; unfold sp in *; lia.
  - exact Hfz.
  - exact Hroom.
  - exact Hrp1.
  - exact Hlen4.
  - exact (proj2 HROOM).
  - exact Huniv.
  - exact H10.
  - exact H11.
  - exact H12.
  - clear - Ho1 HR; unfold sp in *; lia.
  - exact Ho2.
  - clear - Ho1 HR; unfold sp in *; lia.
  - exact Hcho.
  - exact Hout.
  - exact Hled.
  - exact Hsrc.
  - reflexivity.
  - apply Hhome; [exact Hkept | exact Hdisj | exact Hcase |].
    intros b0 m Hin. pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
    destruct (Hall _ Hin) as (_ & HB & _). exact HB.
  - exact HEVc.
  - exact HW1.
  - exact Hhead.
  - exact (proj1 HROOM).
  - exact HFPS. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJp & HWk & HP2 &
  ((Hroom2 & Hrpng & Hrpg & Hret2) & Hmn2)).
rewrite Hc2.
replace (sp + d + (R - (sp + d))) with R in HJp, HWk by (clear; lia).
replace (R + - (R - (sp + d))) with (sp + d) in HJp, HWk by (clear; lia).
idtac "PSTEP-POST".
pose proof (ajxR_ar HJ2) as HAR2.
pose proof (ajxR_img HJp) as HKIMGp. pose proof (ajxR_frm HJp) as HKFRMp. pose proof (ajxR_pres HJp) as HPRESp.
pose proof (@cf_head_nonneg cp) as Hh.
assert (HSTK208 : 208 <= STK_put_string) by (vm_compute; congruence).
assert (HSTKp0 : 0 <= STK_put) by (vm_compute; congruence).
pose proof Hstk as (_ & _ & _ & Hslo' & _).
(* the frame: its place, its shadow *)
assert (HinF : In (0, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ 0 pos HARc HinF) as (_ & (HFa0 & HFa1) & _ & _).
assert (EF : frame_addr lyc 0 pos = frame_addr ly 0 pos) by (unfold frame_addr; rewrite HlyF; reflexivity).
rewrite EF in HFa0, HFa1. change (fs_frame_bytes 0) with 64 in HFa0, HFa1.
destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HARc) as (_ & HFb).
rewrite Forall_forall in HFb. destruct (HFb (0, pos) HinF) as (HF4096 & HFceil). cbn [fst snd] in HF4096, HFceil.
rewrite EF in HF4096, HFceil. change (fs_frame_bytes 0) with 64 in HFceil.
(* the call's footprint: the struct (above sp) and the buffer block (below the ceiling, apart from the frame) *)
assert (Hblkc : WriterApp.w_cap st1 <> 0 -> In (bufc - cf_head, WriterApp.w_cap st1 + cf_head) (ablocks B lyc Sc)).
{ intros Hnz. pose proof (ps_led_blocks _ _ _ _ _ _ _ _ _ _ Hled) as Hall. rewrite Forall_forall in Hall.
  destruct (Hall _ (Hcase Hnz)) as (_ & HB & _). exact HB. }
assert (NFP : forall a,
  (YM05.alloc_ceiling <= a < o \/ (frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64) \/
   (SHADOW_OFF <= a < kHighMemBeg)) -> ~ inFP FPc a).
{ intros a Ha. apply notin_cfp.
  - unfold sp in Ho1. clear - Ha HFceil HC Ho1 Hslo Hceil Hstk0. unfold SHADOW_OFF, kHighMemBeg in *. lia.
  - intros Hnz Hab. pose proof (Hblkc Hnz) as HB.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc HB) as (_ & Hb4096 & Hbceil & Hbapp & _).
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ 0 pos HARc HB HinF) as Hzd.
    unfold zdisjoint in Hzd. cbn [fst snd] in Hzd. rewrite EF in Hzd. change (fs_frame_bytes 0) with 64 in Hzd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    clear - Ha Hab Hzd Hbapp Hbceil HC. lia. }
assert (NFPw : forall a, R <= a < sp -> ~ inFP FPc a).
{ intros a Ha. apply NFP. left. split; [|clear - Ha Ho1; unfold sp in *; lia].
  clear - Ha HR Hslo' Hceil HSTK208. unfold sp in *. lia. }
assert (KW : forall a, R <= a < sp -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply HWk; [clear - Ha Hd0; lia | exact (NFPw a Ha)]. }
assert (KF : forall a, (frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 \/
    PS_SB + frame_addr ly 0 pos / 8 <= a < PS_SB + frame_addr ly 0 pos / 8 + 8) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply (HKFRMp 0 pos a HinF).
  - unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64.
    change (64 / 8) with 8. unfold PS_SB, SHADOW_OFF in Ha |- *. clear - Ha; lia.
  - apply NFP. destruct Ha as [Ha | Ha]; [right; left; exact Ha | right; right].
    unfold PS_SB, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. clear - Ha HFceil HC HF4096. lia. }
(* the writer after P ++ [b] *)
apply prhWriter_ret_open in Hret2.
destruct Hret2 as (ok2 & ran2 & buf2 & Lam2 & peak2 & Hoks2 & Hout2 & Hled2 & Hblk2 & G2).
destruct (prhW_app_model st P [b] ok ok2 most ran ranc ran2 Hcnt0 (ps_led_cnt _ _ _ _ _ _ _ _ _ _ Hled)
  (ps_led_fail _ _ _ _ _ _ _ _ _ _ Hled) Hoks Hoks2) as (okn & Hput & Hoksn & HGn).
fold st1 in Hput.
pose proof (prhW_cap_after P ok st) as Hcapa. fold st1 in Hcapa.
pose proof (prhW_blk_trans B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ps_led_nodup _ _ _ _ _ _ _ _ _ _ Hled) Hcapa Hblk Hblk2)
  as Hblkn.
assert (Hn1 : 0 < Z.of_nat (length bs) + 1) by lia.
assert (Hd1 : WriterApp.w_cap st1 = 0 \/ s + (Z.of_nat (length bs) + 1) <= bufc \/ bufc + WriterApp.w_cap st1 <= s)
  by (clear - Hdisj; lia).
pose proof (kept_at_blk _ _ _ _ _ _ _ _ _ _ _ _ s _ Hblk2 Hn1 Hd1 Hkept) as Hkept2.
idtac "PSTEP-WRITER".
assert (Hclc : ~ YI16.sink_open_fp FPc).
{ apply sink_closed_pos. unfold FPc, prhWriter_cfp, prhWriter_fp.
  constructor; [cbn [fst]; clear - Ho1 Hslo Hceil Hstk0 HC; unfold sp in *; lia|].
  destruct (Z.eqb_spec (WriterApp.w_cap st1) 0) as [Hz0 | Hnz]; [constructor|].
  unfold ablocks_fp. cbn [map]. constructor; [cbn [fst] | constructor].
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc (Hblkc Hnz)) as (_ & H4096 & _). clear - H4096; lia. }
apply (K ly2 S2 Hp2 W2 regs2 mem2 md2 k1).
2: exact HP2.
2: exact KW.
2: { intros a Ha. apply HPRESp. clear - Ha HSTKp0 Hd0; lia. }
2: exact KF.
unfold ps_commonR, ps_saved_ok, ps_okeep, ps_wkeep.
unfold x_R, x_n, x_SHF, x_FL, x_F, x_FP. unfold x_sp.
cbn [x_d x_ly x_S x_Hp x_W x_regs x_mem x_md x_o x_s x_bs x_buf x_st x_Lam x_peak x_ran x_rpsm x_rpx x_rpos x_rpi
  x_rpH0 x_rphist x_most x_own x_fx].
change (spZ regs) with sp. change (PS_R sp) with R.
unfold ps_saved_ok, ps_okeep in Hsav, Hok. unfold x_sp in Hsav, Hok. cbn [x_regs x_o x_W x_mem] in Hsav, Hok.
change (spZ regs) with sp in Hsav, Hok.
unfold ps_wkeep, x_sp, x_FP in Hwk0. cbn [x_regs x_d x_o x_buf x_st x_W x_mem] in Hwk0. change (spZ regs) with sp in Hwk0.
split; [exact HJ2|].
split.
{ rewrite Forall_forall in Hsav |- *. intros pz Hpin. rewrite <- (Hsav pz Hpin). apply rdword_eq_of. intros i Hi.
  assert (Hrg : -104 <= fst pz <= -8).
  { unfold ps_saved_list in Hpin. cbn [In] in Hpin. repeat (destruct Hpin as [<- | Hpin]; [cbn [fst]; lia|]). destruct Hpin. }
  apply KW. clear - Hrg Hi HR. lia. }
split.
{ rewrite <- HF56. apply rdword_eq_of. intros i Hi. apply KF. left. clear - Hi; lia. }
split.
{ intros a Ha1 Ha2. rewrite <- (Hok a Ha1 Ha2). apply HWk; [clear - Ha1 Ha2 HR Ho2; lia|].
  apply NFP. left. split; [clear - Ha2 Hslo Hceil Hstk0; lia | clear - Ha1; lia]. }
split; [exact (PCALL _ _ Hmn2 HPm)|].
split.
{ exists okn, ran2, buf2, Lam2, peak2. rewrite Hput.
  split; [exact (conj Hoksn (HGn G1 G2))|]. split; [exact Hout2|]. split; [exact Hled2|]. split; [exact Hblkn|].
  split; [exact Hkept2|]. split.
  - intros b0 m Hin Hb Hpe.
    assert (Hpe' : s + (Z.of_nat (length bs) + 1) <= b0 + m) by (clear - Hpe; lia).
    exact (blk_kept_at _ _ _ _ _ _ _ _ _ _ _ _ s _ Hblk2 Hn1 Hd1 b0 m (Hlive b0 m Hin Hb Hpe) Hb Hpe').
  - split.
    + pose proof (blk_src_disj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s _ Hblk2 HAR2 Hled2 Hkept Hn1 Hd1) as Hd2.
      clear - Hd2. lia.
    + (* the EXACT position after the put: P's events plus one when the put grew and left the writer not failed
         (ps_len_one), which is the arm tput_specX's per-arm post advances on *)
      pose proof (ps_len_one st P b okn ok ok2 Hput) as LEN. fold st1 in LEN. rewrite LEN.
      pose proof Hout2 as (_ & _ & _ & _ & _ & _ & Hvf2 & Hf012 & _).
      assert (EQS : forall X0 : nat, (rpi + (X0 + 1))%nat = Datatypes.S (rpi + X0)) by (intros; lia).
      destruct (prhWriter_grows st1 b) eqn:Hgr.
      * destruct (Z.eq_dec (WriterApp.w_failed (prhWriter_putN ok2 st1 [b])) 0) as [Hz | Hnz].
        -- destruct (proj1 (Hrpg eq_refl _ Hvf2) Hz) as (h2 & Hpq). exists h2.
           rewrite Hz. cbn [Z.eqb andb]. rewrite EQS. exact Hpq.
        -- assert (Hf1 : WriterApp.w_failed (prhWriter_putN ok2 st1 [b]) = 1) by (clear - Hf012 Hnz; lia).
           destruct (proj2 (Hrpg eq_refl _ Hvf2) Hf1) as (h2 & Hpq). exists h2.
           rewrite (proj2 (Z.eqb_neq _ _) Hnz). cbn [andb]. rewrite Nat.add_0_r. exact Hpq.
      * pose proof (Hrpng eq_refl) as Hpq. exists rph1. cbn [andb]. rewrite Nat.add_0_r. exact Hpq. }
split; [exact Hroom2|].
split.
{ intros a Hro' Ho' He'.
  rewrite (HKIMGp a (in_roP_img a Hro') Ho' He' (HPSTRO a Hro') (fp_spares_closed _ a Hclc)).
  exact (Hro a Hro' Ho' He'). }
(* the caller's window: put's own window keep off its footprint (the struct, and the buffer block below the ceiling) *)
split; [|exact Hfl].
intros a Ha1 Ha2. rewrite <- (Hwk0 a Ha1 Ha2). apply HWk; [clear - Ha1 HR; lia|].
apply notin_cfp.
- intros Hc. apply Ha2. exists (o, o + 32). split; [left; reflexivity | exact Hc].
- intros Hnz Hab. pose proof (Hblkc Hnz) as HB.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARc HB) as (_ & Hb4096 & Hbceil & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  clear - Ha1 Hab Hbceil HC Hslo Hceil Hstk0. lia.
Qed.
(* the entry segment's float clause: at the entry the current float state is the entry's (fpre's FRM0-ENTRY) *)
Lemma ps_float_entry : forall X ch, ps_pre X ch -> x_fx X = fx -> ps_float X.
Proof.
intros X ch Hpre Efx. pose proof Hpre as (HFPRE & _). destruct HFPRE as (_ & _ & _ & _ & Hz).
unfold ps_float. rewrite <- Efx. split; [exact Hz | intros r _; reflexivity].
Qed.
End h.
End f.
End d.
(* ---- the float state across a float-changing call (the internal file REFIT-WRITER.md's design, points 2-3): fregs_kept_x is reflexive
   and transitive (its definition, YCbqG.v:26), and a join's ps_common moves to the call's fx' once the float clause
   holds there (every other conjunct reads no float state). Stated after the Sections, generic in both float
   states. ---- *)
Lemma ps_fk_refl : forall f : YK11.FPState, fregs_kept_x f f.
Proof. intros f r _. reflexivity. Qed.
Lemma ps_fk_trans : forall f1 f2 f3 : YK11.FPState, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.
Section refx. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {SK : YI16.sink_head} {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world (@pa_segs _ A_prog_listing PA) -> (word -> option byte) -> Model -> Prop.
Variable Pm : (word -> option byte) -> Prop.
(* at any world relation R of the join's journal (after a put: wle' SEGS RZ_cf) *)
Lemma ps_common_refxR : forall (R : world (@pa_segs _ A_prog_listing PA) -> world (@pa_segs _ A_prog_listing PA) -> Prop)
  (f f' : YK11.FPState) X pos P lyc Sc Hpc Wc memc mdc kc,
  ps_commonR (fx := f) B ARx Pm R X pos P lyc Sc Hpc Wc memc mdc kc ->
  YK0o.frm_zero (@YK11.fp_csr f') -> fregs_kept_x (x_fx X) f' ->
  ps_commonR (fx := f') B ARx Pm R X pos P lyc Sc Hpc Wc memc mdc kc.
Proof.
intros R f f' X pos P lyc Sc Hpc Wc memc mdc kc (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _) Hz Hk.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj Hz Hk)))))))))).
Qed.
Lemma ps_common_refx : forall (f f' : YK11.FPState) X pos P lyc Sc Hpc Wc memc mdc kc,
  ps_common (fx := f) B ARx Pm X pos P lyc Sc Hpc Wc memc mdc kc ->
  YK0o.frm_zero (@YK11.fp_csr f') -> fregs_kept_x (x_fx X) f' ->
  ps_common (fx := f') B ARx Pm X pos P lyc Sc Hpc Wc memc mdc kc.
Proof. intros f f'. exact (ps_common_refxR (@wle _) f f'). Qed.
End refx.
(* add one region to a listing state: leaves region_ok, then all_disjoint, then the goal with the grown state *)
Ltac add_reg HS r :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let Hok := fresh "Hrok" in let Hdj := fresh "Hrdj" in
    assert (Hok : region_ok segs E (ms_mem ms) r);
    [| assert (Hdj : all_disjoint E r (ss_mem ss));
       [| let H' := fresh "HSn" in pose proof (st_ok_pi_add_region E ss ms r HS eq_refl Hok Hdj) as H';
          clear HS Hok Hdj; rename H' into HS]]
  end.
Ltac pnt_run_to RUNTO HS HJ stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
eapply (RUNTO W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun
| clear Hrun HS HJ; let ms' := fresh "ms" in let mat' := fresh "mat" in let HF := fresh "HF" in let HFr := fresh "HFr" in
  let HG := fresh "HG" in intros ms' mat' HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ; srr_norm_model ]
end
end.
(* the P-carrying run (SRr_run_to_pi_AJx_inv applied to P and its laws): HPM : P (ms_mem ms) passed after HJ and
   re-introduced under the same name for the end memory *)
Ltac pnt_run_to_inv RUNTO HS HJ HPM stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi (@pl_tpi A_prog_listing PL_prog_A) FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
eapply (RUNTO W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ HPM);
[ clear Hrun
| clear Hrun HS HJ HPM; let ms' := fresh "ms" in let mat' := fresh "mat" in let HF := fresh "HF" in
  let HFr := fresh "HFr" in let HG := fresh "HG" in intros ms' mat' HS HJ HPM HF HFr HG;
  cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM; srr_norm_model ]
end
end.
(* a stretch of the tokenless engine stopped at a branch it cannot decide: split on the condition *)
Ltac pnt_branch BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
  let r := eval vm_compute in (sym_step_pi (@pl_tpi A_prog_listing PL_prog_A) ss) in
  lazymatch r with
  | PStop (SR_branch ?c ?a ?b) =>
      apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
  | _ => fail "pnt_branch: the state is not at a branch:" r
  end
end.
(* a byte is outside the write windows of a run's regions: the prologue's (base sp, Usp its value) and segment A's
   (bases SHF, F, R, sp: R513 R39 R34 R2 their values) *)
Ltac nwr0 Usp fin := let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros (r & Hin & Hx); cbn [In ss_mem ps_ss0] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi probe_region saved_region got_regionP bcell_regionP uargot_region
           uarcell_region base_val] in Hx; rewrite ?Usp in Hx; fin Hx | ]); try destruct Hin.
Ltac nwrA R513 R39 R34 R2 fin := let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros (r & Hin & Hx); cbn [In ss_mem] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi fshadow_reg fframe_reg rframe_region saved_region] in Hx;
      rewrite ?R513, ?R39, ?R34, ?R2 in Hx; fin Hx | ]); try destruct Hin.
About kept_at_blk. About blk_kept_at. About kept_at_bounds. About str_notin_fp. About cstr_from_entry.
About str_shadow_at. About kept_at_loc. About val_mem1_of_aview. About ledger_blocks_disj. About blk_src_disj.
About notin_cfp. About ps_chain_arg. About ps_okeep. About SRr_run_to_pi_AJx_inv. About hblock_shadow.
About prhW_out_kept. About prh_ledger_kept. About ps_put_step. About ps_led_blocks. About ps_R_facts.
About ps_common_frame. About ps_common_run.
About ps_entry. About ps_put_call. About ps_pre. About ps_head. About ps_tail. About ps_esc. About ps_next.
About ps_common. About ps_float. About ps_Qfin. About ps_Qin. About ps_fp_closed. About ps_out_own. About ps_call_chain.
About ps_float_entry. About ps_common_refx. About ps_lit_fact. About gcell_pst. About ps_s0. About ps_led_cnt.
About ps_led_fail. About ps_led_nodup. About img_hull_vis. About ps_arodata_keep. About kept_at_nil_lam.
