(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the member loop's helper lemmas of parse_items on image B,
   under parse_items_spec k's entry premises (Section hypotheses, the A walk's list and order).
   B-LOCAL PORT of the helper half of the A walk's lib/A/FSW_parse_items_loop.v (a working branch
   4480a5df1ae, lines 196-745, a Theorem Labs lane) and of lib/A/FSW_parse_items_mem.v's frame lemmas (same commit), renamed
   pi_ -> pil_. Changes, all from image B's registers and frame (FSW_parse_items_seg.v, FSW_parse_items_loop.v):
     - the resume env's base atoms are 9 (s1 = q) and 19 (s3 = v), A's are 8 and 20 (pil_env_at, pil_awr_rgs,
       pil_treg_disj, pil_frameL_of, pil_csL_ok);
     - pil_R_ok admits s0 = x8 too (B keeps q + 16 there, inside pib_R0 / pib_RL) and the atoms 9 / 19 / 32;
     - the frame is pib_frame0 / pib_frameL (saved registers at 136 .. 40, segment C's five locals at 0 .. 32);
     - pil_awr_rgs / pil_submem / pil_start are over FSW_parse_items_seg.pib_rgs / pib_start (write windows narrowed
       per segment), where A's pi_awr_ret / pi_start_T are over the full resume regions;
     - B calls skip_ws, so A's white-space conditions (pi_wsc, pi_conds_ws) are replaced by the one guard
       in->p < in->end (pil_conds_wsc0).
   rule 24: proves no function (kind: helper lemmas). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_kit FSW_parse_items_mdl FSW_parse_items_seg FSW_parse_items_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require FSW_pj_set_heads FSW_grow_holds.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= image-free facts of the frame and the env (FSW_parse_items_mem.v's, re-read on B) ========== *)
(* the frame's saved words as the chunks of pi_cs, under an env whose xatoms 3 .. 15 hold them *)
Lemma pil_cs0_ok : forall E m sp0 xr, length xr = 13%nat ->
  (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0)) ->
  pib_frame0 m sp0 xr -> Forall (YP09.chunk_ok tfibsegs E m (sp0 - 144)) pi_cs.
Proof.
intros E m sp0 xr Hl HX HF. unfold pib_frame0 in HF. cbn [seq] in HF.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
unfold pi_cs.
repeat (apply Forall_cons; [
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff (xatom ?j) 0))) =>
    let i := eval vm_compute in (j - 3)%nat in
    apply (chunk_ok_val tfibsegs _ _ _ off 8 _ (bv_unsigned (nth i xr (Z_to_bv 64 0))));
    [ rewrite fsw_SOff0; change j with (3 + i)%nat; rewrite (HX i ltac:(lia)); symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range | cbn; lia
    | lazymatch goal with H : val_mem _ _ (_ - 8 - 8 * Z.of_nat i) _ _ |- _ =>
        cbn [Z.of_nat] in H; replace (sp0 - 144 + off) with (sp0 - 8 - 8 * Z.of_nat i) by (cbn [Z.of_nat]; lia);
        cbn [Z.of_nat]; exact H end ] end|]).
apply Forall_nil.
Qed.
(* the shadow-cell expression's value *)
Lemma pil_shx_denot : forall E b x c, ew E b = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= x -> 0 <= c -> x + c < 2 ^ 47 -> sv_denot E (pi_shx b c) = Z_to_bv 64 (pi_sh (x + c)).
Proof.
intros E b x c Eb E32 Hx Hc Hxc. apply bv_eq.
change (bv_unsigned (sv_denot E (pi_shx b c))) with (YP0e.U E (pi_shx b c)). unfold pi_shx.
rewrite (pi_U_shadow E b c x Eb Hx Hc Hxc E32).
assert (Hs : 0 <= pi_sh (x + c) < 2 ^ 64).
{ unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos (x + c) 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound (x + c) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
rewrite unsigned_lit_small by exact Hs. reflexivity.
Qed.
(* the member loop's frame chunks (pib_csL) under a resume env *)
Lemma pil_csL_ok : forall E m sp0 xr qq vv, length xr = 13%nat ->
  (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0)) ->
  ew E 19 = Z_to_bv 64 vv -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= vv -> vv + 56 <= 2 ^ 47 ->
  pib_frameL m sp0 xr qq vv -> Forall (YP09.chunk_ok tfibsegs E m (sp0 - 144)) pib_csL.
Proof.
intros E m sp0 xr qq vv Hl HX E19 E32 Hv0 Hv1 (HF0 & F0 & F8 & F16 & F24 & F32).
unfold pib_csL. apply Forall_app. split; [|exact (pil_cs0_ok E m sp0 xr Hl HX HF0)].
assert (Hsh : forall y, 0 <= y < 2 ^ 47 -> 0 <= pi_sh y < 2 ^ 64).
{ intros y Hy. unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 0 8 (SLit 1152921504606846976) 1152921504606846976);
    [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact F0].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 8 8 (pi_shx 19 32) (pi_sh (vv + 32)));
    [apply pil_shx_denot; [exact E19 | exact E32 | lia | lia | lia]
    | cbn; pose proof (Hsh (vv + 32) ltac:(lia)); lia | cbn; lia
    | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; exact F8].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 16 8 (SOff 19 32) (vv + 32));
    [apply bv_eq; rewrite denot_SOff, E19, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
    | cbn; lia | cbn; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; exact F16].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 24 8 (pi_shx 19 24) (pi_sh (vv + 24)));
    [apply pil_shx_denot; [exact E19 | exact E32 | lia | lia | lia]
    | cbn; pose proof (Hsh (vv + 24) ltac:(lia)); lia | cbn; lia
    | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; exact F24].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 32 8 (SOff 19 24) (vv + 24));
    [apply bv_eq; rewrite denot_SOff, E19, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
    | cbn; lia | cbn; lia | replace (sp0 - 144 + 32) with (sp0 - 112) by lia; exact F32].
Qed.
(* the resume env's saved-register atoms (pib_xs / pib_xsK) *)
Lemma pil_xs_saved : forall regs' p e d xr k' y' n cap' j, length xr = 13%nat -> (j < 13)%nat ->
  ew (Ereg regs' (fs_extraT ++ pib_xs p e d xr k' y' n cap')) (xatom (3 + j)) = nth j xr (Z_to_bv 64 0).
Proof.
intros regs' p e d xr k' y' n cap' j Hl Hj. rewrite fsw_ew_xatom. unfold pib_xs.
change ([Z_to_bv 64 p; Z_to_bv 64 e; Z_to_bv 64 d] ++ xr ++ ?t) with
  (Z_to_bv 64 p :: Z_to_bv 64 e :: Z_to_bv 64 d :: xr ++ t).
change (nth (3 + j) (?a :: ?b :: ?c :: ?l) ?z) with (nth j l z).
rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma pil_xsK_saved : forall regs' p e d xr k' y' n cap' a kl j, length xr = 13%nat -> (j < 13)%nat ->
  ew (Ereg regs' (fs_extraT ++ pib_xsK p e d xr k' y' n cap' a kl)) (xatom (3 + j)) = nth j xr (Z_to_bv 64 0).
Proof.
intros regs' p e d xr k' y' n cap' a kl j Hl Hj. rewrite fsw_ew_xatom. unfold pib_xsK, pib_xs.
change (([Z_to_bv 64 p; Z_to_bv 64 e; Z_to_bv 64 d] ++ xr ++ ?t) ++ ?u) with
  (Z_to_bv 64 p :: Z_to_bv 64 e :: Z_to_bv 64 d :: (xr ++ t) ++ u).
change (nth (3 + j) (?a :: ?b :: ?c :: ?l) ?z) with (nth j l z).
rewrite app_nth1 by (rewrite length_app; lia). rewrite app_nth1 by lia. reflexivity.
Qed.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved_regs.
#[local] Abbreviation JC := (pib_jc B k ly S U W regs mem md ot v).
#[local] Abbreviation RP := (pib_regsP B regs q v).
#[local] Abbreviation STKP := (pib_stack k ly W regs mem q ot text len tb).
#[local] Abbreviation BLK := (pib_blocks B ly S U v text len tcap live peak cnt fail).
#[local] Abbreviation OBJ := (pib_obj v).

(* ================= the entry premises (parse_items_spec k's, all of them; the A walk's list) ================= *)
Variable ch : list (Z * Z * Z).
Hypothesis Hk : (k <= 1)%nat.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HPRE : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch.
Hypothesis HHEADS : FSupoisonU.fs_heads B ly S U.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HQ16 : spZ regs + 16 <= q.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HIN0 : PjIn.pj_in_ok tfibsegs (rdW W mem) q text len p dd tb.
Hypothesis HVTX : v + 56 <= text - HEAD \/ text + tcap <= v.
Hypothesis HPO0 : pobj tfibsegs B ly S W mem v.
Hypothesis HQT : quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))).
Hypothesis HSZ : rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)).
Hypothesis HLIVE : live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64.
Hypothesis HEV : st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX.
Hypothesis HBB : blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1).
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis H11 : YK11.getr regs 11 = w64 v.
Hypothesis H12 : YK11.getr regs 12 = w64 1.
Hypothesis HCH0 : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Hypothesis HREST : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest.
Hypothesis HDV : FSDocStrs.fs_doc_values (PjTree.JObj ms).
Hypothesis HDS : FSDocStrs.fs_doc_strings (PjTree.JObj ms).
Hypothesis HWF : PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms).
Hypothesis HDEP : (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat.
Hypothesis HZERO : PjStruct.pj_zero tfibsegs (rdW W mem) v.
Hypothesis HVSP : v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.

(* ================= small facts of the entry ================= *)
Lemma pil_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof.
pose proof (fsw_sp B _ ly S U W regs mem md ch (proj1 HPRE)) as (H1 & H2 & H3 & _). unfold sp0. lia.
Qed.
Lemma pil_stk144 : 144 <= STK_parse_items (1 - k).
Proof.
assert (HF : FRAME_parse_items <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
change FRAME_parse_items with 144 in HF. exact HF.
Qed.
Lemma pil_xr_len : length xr = 13%nat.
Proof. unfold xr. rewrite length_map. reflexivity. Qed.
Lemma pil_v_rng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
exact (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO0).
Qed.

(* ================= the resume env of a call ================= *)
Local Ltac pil_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; unfold acallee_saved; lia.
Lemma pil_kept : forall regsC regs' (r : bv 5), aregs_preserved regsC regs' ->
  acallee_saved (bv_unsigned r) -> YK11.getr regs' r = YK11.getr regsC r.
Proof. intros regsC regs' r HP Hr. exact (fsw_pres regsC regs' r HP Hr). Qed.
(* the resume env's atoms 2 / 3 / 4 / 9 / 19 / 32 *)
Lemma pil_env_at : forall regsC regs' xs R, RP regsC R -> aregs_preserved regsC regs' ->
  ew (Ereg regs' (fs_extraT ++ xs)) 9 = Z_to_bv 64 q /\ ew (Ereg regs' (fs_extraT ++ xs)) 19 = Z_to_bv 64 v /\
  ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF /\
  bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - 144 /\
  ew (Ereg regs' (fs_extraT ++ xs)) 3 = Z_to_bv 64 (as_gp B) /\ ew (Ereg regs' (fs_extraT ++ xs)) 4 = Z_to_bv 64 (as_tp B).
Proof.
intros regsC regs' xs R (Rsp & R9 & R19 & R3 & R4 & _) HP.
rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), (ew_Ereg_nat regs' _ 19 19%bv eq_refl),
  (ew_Ereg_nat regs' _ 2 2%bv eq_refl), (ew_Ereg_nat regs' _ 3 3%bv eq_refl), (ew_Ereg_nat regs' _ 4 4%bv eq_refl).
change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
rewrite (pil_kept regsC regs' 9%bv HP ltac:(pil_acs)), (pil_kept regsC regs' 19%bv HP ltac:(pil_acs)),
  (pil_kept regsC regs' 2%bv HP ltac:(pil_acs)), (pil_kept regsC regs' 3%bv HP ltac:(pil_acs)),
  (pil_kept regsC regs' 4%bv HP ltac:(pil_acs)).
unfold spZ in Rsp. repeat split; assumption.
Qed.
(* the callee-saved list R restated at the resume: each register callee-saved (s0, s1, s2 .. s11), each value naming
   only q (9), v (19) and the shadow base (32) *)
Definition pil_R_ok (R : list (bv 5 * sv)) : bool :=
  forallb (fun r => negb (Z.eqb (bv_unsigned (fst r)) 0) && negb (Z.eqb (bv_unsigned (fst r)) 10) &&
    ((Z.eqb (bv_unsigned (fst r)) 8) || (Z.eqb (bv_unsigned (fst r)) 9) ||
     ((18 <=? bv_unsigned (fst r)) && (bv_unsigned (fst r) <=? 27))) &&
    forallb (fun n => Nat.eqb n 9 || Nat.eqb n 19 || Nat.eqb n 32) (pik_sv_atoms (snd r))) R.
Lemma pil_R0_ok : pil_R_ok pib_R0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pil_RL_ok : pil_R_ok pib_RL = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pil_setr_ok : forall regsC regs' xs R e10, RP regsC R -> aregs_preserved regsC regs' -> pil_R_ok R = true ->
  YK11.getr regs' 10 = sv_denot (Ereg regs' (fs_extraT ++ xs)) e10 ->
  Forall (fun r => fst r <> 0%bv /\ YK11.getr regs' (fst r) = sv_denot (Ereg regs' (fs_extraT ++ xs)) (snd r))
    ((10%bv, e10) :: R).
Proof.
intros regsC regs' xs R e10 HR HP Hok Ha0.
pose proof (pil_env_at regsC regs' xs R HR HP) as (E9 & E19 & E32 & _).
pose proof HR as (_ & R9 & R19 & _ & _ & RL).
constructor; [split; [intros E; discriminate E | exact Ha0]|].
unfold pil_R_ok in Hok. rewrite forallb_forall in Hok. rewrite Forall_forall in RL |- *.
intros [r e] Hin. pose proof (Hok _ Hin) as Hb. pose proof (RL _ Hin) as Hr. cbn [fst snd] in *.
apply andb_prop in Hb as [Hb Hat]. apply andb_prop in Hb as [Hb Hcs]. apply andb_prop in Hb as [H0 _].
split.
- intros ->. discriminate H0.
- rewrite (pil_kept regsC regs' r HP).
  + rewrite Hr. apply pik_sv_denot_agree; [reflexivity|].
    intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
    apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
    * rewrite (ew_Ereg_nat regsC _ 9 9%bv eq_refl), R9. symmetry. exact E9.
    * rewrite (ew_Ereg_nat regsC _ 19 19%bv eq_refl), R19. symmetry. exact E19.
    * change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
      rewrite <- E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  + unfold acallee_saved. apply orb_prop in Hcs as [Hcs|Hcs]; [apply orb_prop in Hcs as [Hcs|Hcs]|].
    * apply Z.eqb_eq in Hcs. lia.
    * apply Z.eqb_eq in Hcs. lia.
    * apply andb_prop in Hcs as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. lia.
Qed.

(* the same without a0 *)
Lemma pil_setr_R : forall regsC regs' xs R, RP regsC R -> aregs_preserved regsC regs' -> pil_R_ok R = true ->
  Forall (fun r => fst r <> 0%bv /\ YK11.getr regs' (fst r) = sv_denot (Ereg regs' (fs_extraT ++ xs)) (snd r)) R.
Proof.
intros regsC regs' xs R HR HP Hok.
pose proof (pil_setr_ok regsC regs' xs R (SOff 10 0) HR HP Hok) as H.
assert (Ha0 : YK11.getr regs' 10 = sv_denot (Ereg regs' (fs_extraT ++ xs)) (SOff 10 0))
  by (rewrite fsw_SOff0; symmetry; exact (ew_Ereg_nat regs' _ 10 10%bv eq_refl)).
exact (Forall_inv_tail (H Ha0)).
Qed.

(* ================= the call premises every step needs ================= *)
Lemma pil_pin_vals : forall m qq pc d, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  val_mem tfibsegs m qq 8 pc /\ val_mem tfibsegs m (qq + 8) 8 (text + len) /\ val_mem tfibsegs m (qq + 16) 4 d.
Proof.
intros m qq pc d H. pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ H) as (Hq0 & Hq64 & Ht0 & Hp & Hte & _ & _ & _ & Hd).
destruct H as (Bp & Be & Bd & _).
split; [apply fsw_pj_u64_val; split; [lia | exact Bp]|].
split; [apply fsw_pj_u64_val; split; [lia | exact Be]|].
apply (proj2 (fsw_pj_word4_iff tfibsegs m (qq + 16) d ltac:(lia) ltac:(lia))). exact Bd.
Qed.
Lemma pil_text_rng : forall lyc Sc (W1 : world tfibsegs) mx mdx memC pc d,
  AR tfibsegs B lyc Sc W1 mx mdx -> rd_text tfibsegs B lyc Sc W1 memC text len tcap ->
  PjIn.pj_in_ok tfibsegs (rdW W1 memC) q text len pc d tb ->
  4096 + HEAD <= text /\ text <= pc <= text + len /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
intros lyc Sc W1 mx mdx memC pc d HAR (Ht & Hb & Hl) HIN.
destruct (fsw_rblock_low B lyc Sc W1 mx mdx _ text tcap HAR Hb) as (_ & H2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Hp & _).
pose proof asan_consts as (C1 & _). lia.
Qed.
Lemma pil_rd_sum_nn : forall lyc Sc (W1 : world tfibsegs) memC L, rd_blocks_ok tfibsegs B lyc Sc W1 memC L -> 0 <= rd_sum L.
Proof.
intros lyc Sc W1 memC L. induction L as [|[a kk] L IH]; intros H; [unfold rd_sum; cbn; lia|].
unfold rd_sum in *. cbn [fold_right fst snd].
assert (Hkk : 0 < kk) by (destruct (H a kk (or_introl eq_refl)) as (_ & _ & Hk0 & _); exact Hk0).
assert (HL : rd_blocks_ok tfibsegs B lyc Sc W1 memC L) by (intros a' k' Hin; apply H; right; exact Hin).
pose proof (IH HL). lia.
Qed.
Lemma pil_not_entry : forall lyc Sc (W1 : world tfibsegs) mx mdx L, AR tfibsegs B lyc Sc W1 mx mdx ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  forall b, In b (rd_hblocks L) -> ~ In b (ablocks B ly S).
Proof.
intros lyc Sc W1 mx mdx L HAR HP b Hb He.
pose proof (FSW_pj_set_heads.pSh_ablocks_nodup B lyc Sc W1 mx mdx HAR) as ND.
apply (Permutation_NoDup HP) in ND. apply (proj2 (NoDup_ListNoDup _)) in ND.
exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ ND He Hb).
Qed.
Lemma pil_slots_of : forall lyc Sc Uc (W1 : world tfibsegs) memC mdC Da T peak1 n kids keys cap dn Di,
  ARU tfibsegs B lyc Sc Uc W1 memC mdC ->
  BLK lyc Sc Uc W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) Da T peak1 ->
  OBJ W1 memC (parse_items_shape.pis_slots true kids keys cap ++ Di) n kids keys cap dn Di -> 0 <= cap ->
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap in
  PjStruct.pj_slots_at (fun a kk => In (a, kk) Dold0) 6 kids keys (Z.of_nat (length dn)) cap /\
  rd_blocks_ok tfibsegs B lyc Sc W1 memC Dold0 /\ PjStruct.pj_apart Dold0 v /\
  incl (rd_heads Dold0) Uc /\ (forall b, In b (rd_hblocks Dold0) -> ~ In b (ablocks B ly S)) /\
  rd_sum Dold0 <= PjGrammar.held T.
Proof.
intros lyc Sc Uc W1 memC mdC Da T peak1 n kids keys cap dn Di HARU
  (_ & _ & HBL & HPERM & HUc & HDa & HSUM & _) (_ & HOP) Hcap0 Dold0.
assert (ES : parse_items_shape.pis_slots true kids keys cap = Dold0) by reflexivity.
assert (HIN : forall b, In b Dold0 -> In b (parse_items_shape.pis_slots true kids keys cap ++ Di))
  by (intros b Hb; apply in_or_app; left; rewrite ES; exact Hb).
pose proof HOP as (HN & HA & _ & HSL & _).
split.
{ apply (parse_items_shape.pis_slots_at_mv (ReaderRes.lin (parse_items_shape.pis_slots true kids keys cap ++ Di))
    (fun a kk => In (a, kk) Dold0) true kids keys (Z.of_nat (length dn)) (Z.of_nat (length dn)) cap HSL);
    [destruct HSL as (_ & Hc & _); lia | exact Hcap0 | intros a kk Hak; rewrite <- ES; exact Hak]. }
split; [intros a kk Hak; exact (HBL a kk (HIN _ Hak))|].
split; [intros b x Hb; exact (HA b x (HIN b Hb))|].
split.
{ intros h Hh. rewrite HUc. apply in_or_app. right. unfold rd_heads in *.
  apply in_map_iff in Hh as (b & <- & Hb). apply (in_map (fun b => (fst b - HEAD, HEAD))).
  exact (Permutation_in _ (Permutation_sym HDa) (HIN b Hb)). }
split.
{ intros b Hb. pose proof HARU as (HAR & _). apply (pil_not_entry lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks in *. apply in_map_iff in Hb as (b0 & <- & Hb0). apply (in_map (fun b => (fst b - HEAD, snd b + HEAD))).
  exact (HIN b0 Hb0). }
assert (HD : 0 <= rd_sum Di)
  by (apply (pil_rd_sum_nn lyc Sc W1 memC Di); intros a kk Hak; apply HBL; apply in_or_app; right; exact Hak).
rewrite pim_rd_sum_app in HSUM. rewrite ES in HSUM. lia.
Qed.
Lemma pil_rd_sum_perm : forall a b, Permutation a b -> rd_sum a = rd_sum b.
Proof. intros a b HP. induction HP; unfold rd_sum in *; cbn [fold_right] in *; lia. Qed.
Lemma pil_rd_sum_hb : forall L, rd_sum (rd_hblocks L) = rd_sum L + HEAD * Z.of_nat (length L).
Proof.
induction L as [|[a kk] L IH]; [reflexivity|]. unfold rd_sum, rd_hblocks in *. cbn [map fold_right fst snd length] in *.
rewrite IH. lia.
Qed.
Lemma pil_budget : forall lyc Sc L T X Y,
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ X ++ Y ->
  st_nev Sc <= st_nev S + rd_ev T ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  rd_sum L = PjGrammar.held T -> (length L <= length T)%nat ->
  quiet (cnt + Z.of_nat (length T)) fail (Z.of_nat (length X)) /\
  live + PjGrammar.held T + rd_live X < 2 ^ 64 /\
  st_nev Sc + rd_ev X <= EV_MAX /\ blocks_bytes Sc + rd_live X <= LIVE_MAX /\ rd_sizes_ok X.
Proof.
intros lyc Sc L T X Y Htr Hnev HP HS HL.
pose proof HQT as HQT'. pose proof HSZ as HSZ'. pose proof HLIVE as HLIVE'. pose proof HEV as HEV'. pose proof HBB as HBB'.
rewrite Htr in HQT', HSZ', HLIVE', HEV', HBB'.
rewrite !length_app, !Nat2Z.inj_add in HQT'.
apply pim_sizes_app in HSZ' as [_ HSZ']. apply pim_sizes_app in HSZ' as [HSZ' _].
rewrite !pim_rd_live_app in HLIVE', HBB'. rewrite !pim_rd_ev_app in HEV'.
pose proof (pim_held_live T) as HHL. pose proof (pim_D_live L T HS HL) as HDL.
pose proof (pim_rd_live_nn Y) as HY1. pose proof (pim_rd_ev_nn Y) as HY2.
assert (BB : blocks_bytes Sc = blocks_bytes S + rd_sum L + HEAD * Z.of_nat (length L)).
{ rewrite (FSW_grow_holds.grow_bb B lyc Sc), (FSW_grow_holds.grow_bb B ly S), (pil_rd_sum_perm _ _ HP),
    pim_rd_sum_app, pil_rd_sum_hb. lia. }
split; [|split; [unfold HEAD in *; lia|split; [lia|split; [unfold HEAD in *; lia | exact HSZ']]]].
destruct (pim_quiet_split cnt fail (Z.of_nat (length T)) (Z.of_nat (length X) + Z.of_nat (length Y))
  ltac:(lia) ltac:(lia) HQT') as [_ HQ2].
destruct (pim_quiet_split (cnt + Z.of_nat (length T)) fail (Z.of_nat (length X)) (Z.of_nat (length Y))
  ltac:(lia) ltac:(lia) HQ2) as [HQ3 _].
exact HQ3.
Qed.

(* ================= the text and struct pj_in ================= *)
Lemma pil_txt_bytes : forall m qq pc d bs more, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  ReaderRes.rest_at tb text pc = bs ++ more ->
  Forall (fun c => 0 <= c < 256) bs /\
  (forall i, (i < length bs)%nat -> mbyte tfibsegs m (pc + Z.of_nat i) = Some (Z_to_bv 8 (nth i bs 0))).
Proof.
intros m qq pc d bs more HIN HR.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Hp & _).
pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Bt0 & Bt1 & Bt) & _).
assert (KEY : forall i, (i < length bs)%nat -> exists b : byte, mbyte tfibsegs m (pc + Z.of_nat i) = Some b /\
  bv_unsigned b = nth i bs 0).
{ intros i Hi.
  assert (E : nth_error (ReaderRes.rest_at tb text pc) i = Some (nth i bs 0))
    by (rewrite HR, nth_error_app1 by exact Hi; apply nth_error_nth'; exact Hi).
  unfold ReaderRes.rest_at, ReaderRes.zb in E. rewrite nth_error_map, nth_error_skipn in E.
  destruct (nth_error tb (Z.to_nat (pc - text) + i)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. exists b. split; [|exact E].
  assert (Hj : (Z.to_nat (pc - text) + i < length tb)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
  pose proof (Bt _ Hj) as Hb. rewrite Eb in Hb.
  replace (text + Z.of_nat (Z.to_nat (pc - text) + i)) with (pc + Z.of_nat i) in Hb by lia. exact Hb. }
split.
- apply Forall_forall. intros c Hc. apply (In_nth bs c 0) in Hc as (i & Hi & <-).
  destruct (KEY i Hi) as (b & _ & Eb). rewrite <- Eb. pose proof (bv_unsigned_in_range 8 b) as Hr.
  unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. lia.
- intros i Hi. destruct (KEY i Hi) as (b & Hm & Eb). rewrite Hm, <- Eb, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma pil_pin_kept : forall m m' qq pc d, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  (forall x, qq <= x < qq + 24 -> mbyte tfibsegs m' x = mbyte tfibsegs m x /\
     (writable_at tfibsegs m x -> writable_at tfibsegs m' x)) ->
  (forall x, text <= x < text + len -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  PjIn.pj_in_ok tfibsegs m' qq text len pc d tb.
Proof.
intros m m' qq pc d HIN HQ HT.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Hq0 & Hq64 & _ & _ & _ & _ & Hlt & _).
destruct HIN as (B1 & B2 & B3 & (W0 & W1 & W2) & H5 & H6 & H7 & H8 & H9 & B10 & Hi11 & Hi12).
assert (KB : forall a bs, Mem.bytes_at tfibsegs m a bs -> (forall x, a <= x < a + Z.of_nat (length bs) ->
  mbyte tfibsegs m' x = mbyte tfibsegs m x) -> Mem.bytes_at tfibsegs m' a bs).
{ intros a bs (A0 & A1 & A2) Hkp. split; [exact A0|]. split; [exact A1|]. intros i Hi.
  change (Mem.mrd tfibsegs m' (Mem.wa (a + Z.of_nat i))) with (mbyte tfibsegs m' (a + Z.of_nat i)).
  rewrite (Hkp (a + Z.of_nat i) ltac:(lia)). exact (A2 i Hi). }
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj Hi11 Hi12))))))))))).
- apply KB; [exact B1|]. intros x Hx. rewrite Mem.length_le8 in Hx. apply HQ. lia.
- apply KB; [exact B2|]. intros x Hx. rewrite Mem.length_le8 in Hx. apply HQ. lia.
- apply KB; [exact B3|]. intros x Hx. rewrite Mem.length_le4 in Hx. apply HQ. lia.
- split; [exact W0|]. split; [exact W1|]. intros i Hi.
  pose proof (W2 i Hi) as Hw. destruct (HQ (qq + i) ltac:(lia)) as (_ & Hwr). apply Hwr. exact Hw.
- apply KB; [exact B10|]. intros x Hx. apply HT. lia.
Qed.
(* the guard in->p < in->end (pib_wsc0) *)
Lemma pil_conds_wsc0 : forall E c0 e, ew E (xatom 0) = Z_to_bv 64 c0 -> ew E (xatom 1) = Z_to_bv 64 e ->
  0 <= c0 -> c0 < e -> e < 2 ^ 62 -> conds_ok E pib_wsc0.
Proof.
intros E c0 e H0 H1 Hc0 Hlt He. unfold pib_wsc0. cbn [conds_ok].
split; [apply (pik_cond_ltu E _ _ 0 0 c0 e H0 H1); lia | exact I].
Qed.

(* ================= the shadow entries of a member-loop run ================= *)
Lemma pil_q_stack : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\ q + 24 <= 2 ^ 47.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & _ & Hotly & _).
pose proof pil_sp0 as (_ & HceilS & _). pose proof pil_stk144.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & _ & _ & _ & _ & Hq8 & _).
lia.
Qed.
Lemma pil_sh_q : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat),
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> ly_stk_lo lyc = ly_stk_lo ly -> ly_stk_hi lyc = ly_stk_hi ly ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = q ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b 0 24).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b HARU Hlo Hhi UB Uq.
pose proof pil_q_stack as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof asan_consts as (C1 & _).
pose proof HARU as (HAR & _).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b q 24 q 0 24);
  [ apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) lyc Sc Uc W1 mem1 md1 (w_H W1) q 24 HARU
      ltac:(lia) ltac:(lia)));
    exact (pi_RA_stack B lyc Sc W1 (unpoison Uc mem1) md1 q 24 HAR ltac:(lia) ltac:(lia) Hq8 ltac:(reflexivity) ltac:(lia))
  | exact UB | exact Uq | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
Qed.
Lemma pil_sh_v : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat),
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> pobj tfibsegs B lyc Sc W1 mem1 v ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = v ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b 0 56).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b HARU HPO UB Uv. pose proof HARU as (HAR & _).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b v 56 v 0 56);
  [ destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr | exact UB | exact Uv | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx.
exact (fsw_pobj_off_shadow B lyc Sc W1 (unpoison Uc mem1) md1 mem1 v HAR HPO x ltac:(lia)).
Qed.
Lemma pil_sh_blk : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat) P nn z lo hi,
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> FSupoisonU.fs_heads B lyc Sc Uc ->
  In (P, nn) (ablocks B lyc Sc) -> P + HEAD <= z + lo -> lo <= hi -> z + hi <= P + nn ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = z ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b lo hi).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b P nn z lo hi HARU HHD Hin H1 H2 H3 UB Uz. pose proof HARU as (HAR & _).
destruct (fsw_ablock_low B lyc Sc W1 (unpoison Uc mem1) md1 P nn HAR Hin) as (L1 & L2 & L3).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b (z + lo) (hi - lo) z lo hi);
  [ apply (fsw_block_body_addressable B lyc Sc Uc W1 mem1 md1 P nn (z + lo) (hi - lo) HARU HHD Hin);
      unfold HEAD in *; lia
  | exact UB | exact Uz | lia | lia |].
intros x Hx. rewrite (Z.min_l lo hi H2), (Z.max_r lo hi H2) in Hx.
apply (fsw_ablock_off_shadow B lyc Sc W1 (unpoison Uc mem1) md1 P nn HAR Hin x). unfold HEAD in *. lia.
Qed.

(* ================= the write windows of a segment's start state ================= *)
Lemma pil_awr_ro : forall E ex rs STK0 sp1 FP0 bl0 blc lyc own fr0,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) ex -> awr_ok tfibsegs B E rs STK0 sp1 FP0 bl0 blc lyc own fr0 ->
  awr_ok tfibsegs B E (ex ++ rs) STK0 sp1 FP0 bl0 blc lyc own fr0.
Proof.
intros E ex rs STK0 sp1 FP0 bl0 blc lyc own fr0 HF H. induction HF as [|r ex Hr HF IH]; [exact H|].
cbn [app]. apply awr_ok_cons_ro; [exact Hr | exact IH].
Qed.
Lemma pil_awr_rgs : forall E lyc Sc (W1 : world tfibsegs) mx mdx memX ex cs fw qw vw,
  AR tfibsegs B lyc Sc W1 mx mdx -> pobj tfibsegs B lyc Sc W1 memX v -> frames Sc = frames S ->
  bv_unsigned (ew E 2) = sp0 - 144 -> bv_unsigned (ew E 9) = q -> bv_unsigned (ew E 19) = v ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) ex ->
  0 <= fst fw -> snd fw <= 144 -> 0 <= fst qw -> snd qw <= 24 -> 0 <= fst vw -> snd vw <= 56 ->
  awr_ok tfibsegs B E (ex ++ pib_rgs cs fw qw vw) STKt ot FP (ablocks B ly S) (ablocks B lyc Sc) lyc [] (frames S).
Proof.
intros E lyc Sc W1 mx mdx memX ex cs fw qw vw HAR HPO Hfr E2 E9 E19 Hex Hf1 Hf2 Hq1 Hq2 Hv1 Hv2.
apply pil_awr_ro; [exact Hex|].
pose proof pil_stk144 as Hst. pose proof HWIN as (Hsq & Hq24 & _ & _ & _). pose proof pil_sp0 as (_ & HceilS & _).
unfold pib_rgs.
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := sp0 - 144 - ot);
  [reflexivity | cbn [YP09.r_base]; rewrite E2; lia
  | cbn [YP09.r_wlo]; unfold STKt; lia | cbn [YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
eapply awr_ok_cons_stack_off with (n := 9%nat) (d := q - ot);
  [reflexivity | cbn [YP09.r_base]; rewrite E9; lia
  | cbn [YP09.r_wlo]; unfold STKt; lia | cbn [YP09.r_whi]; lia |].
eapply awr_ok_cons_gen with (k := 19%nat) (b := v);
  [reflexivity | exact E19 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
assert (HFP : inFP FP a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
destruct HPO as [[((cid & pos & Hin & Hcid & Hal & H1 & H2) & _ & _) | ((b & m & Hin & H1 & H2) & _ & _)] _].
- right. right. split; [exact HFP|]. exists cid, pos. split; [rewrite <- Hfr; exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- left. right. left. split; [exact HFP|]. exists b, m. split; [exact Hin | unfold HEAD in *; lia].
Qed.

(* ================= reading the stop of a segment run ================= *)
Lemma pil_ew_extK : forall ws E K n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
induction ws as [|w ws IH]; intros E K n H; cbn [extK]; [reflexivity|].
rewrite IH by lia. apply ew_ewset_other. lia.
Qed.
Lemma pil_ed_extK : forall ws E K, ed (extK E K ws) = ed E.
Proof. induction ws as [|w ws IH]; intros E K; cbn [extK]; [reflexivity|]. rewrite IH. apply ed_ewset. Qed.
Lemma pil_regs_of_stop : forall E ss ms' (H : word -> bool) l, st_ok tfibsegs E ss (restrict H ms') ->
  pib_regs_are ss l = true -> Forall (fun r => YK11.getr (ms_regs ms') (fst r) = sv_denot E (snd r)) l.
Proof.
intros E ss ms' H l HS Hl. unfold pib_regs_are in Hl. rewrite forallb_forall in Hl.
apply Forall_forall. intros [r e] Hin. pose proof (Hl _ Hin) as Hb. cbn [fst snd] in *.
apply sv_eqb_eq in Hb. rewrite (st_ok_restrict_reg tfibsegs H E ss ms' r HS), Hb. reflexivity.
Qed.
(* the member loop's frame (pib_frameL) read off a frame region at a stop *)
Lemma pil_frameL_of : forall E m wlo whi cs',
  bv_unsigned (ew E 2) = sp0 - 144 -> ew E 19 = Z_to_bv 64 v ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0)) ->
  region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) 0 144 wlo whi cs') -> incl pib_csL cs' ->
  pib_frameL m sp0 xr q v.
Proof.
intros E m wlo whi cs' E2 E19 E32 EX HR Hinc.
pose proof asan_consts as (C1 & _).
assert (Hv : 0 <= v /\ v + 56 < 2 ^ 47) by (pose proof pil_v_rng; lia).
assert (F : forall off e x, In (YP09.mkChunk off (CVal 8 e)) pib_csL -> sv_denot E e = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> val_mem tfibsegs m (sp0 - 144 + off) 8 x).
{ intros off e x Hin He Hx. exact (fsw_field E m 2 (sp0 - 144) cs' 0 144 wlo whi off 8 e x HR E2 (Hinc _ Hin) He
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Hsh : forall y, 0 <= y < 2 ^ 47 -> 0 <= pi_sh y < 2 ^ 64).
{ intros y Hy. unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
split.
- unfold pib_frame0. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 - 144 + (136 - 8 * Z.of_nat j)) by lia.
  apply (F _ (SOff (xatom (3 + j)) 0)); [| rewrite fsw_SOff0, EX by lia; symmetry; apply Z_to_bv_bv_unsigned | apply u64_range].
  unfold pib_csL. apply in_or_app. right. unfold pi_cs.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]; cbn [Z.of_nat]; try lia; cbn [In]; tauto.
- split; [replace (sp0 - 144) with (sp0 - 144 + 0) at 1 by lia; apply (F 0 (SLit 1152921504606846976));
    [cbn; tauto | reflexivity | lia]|].
  split; [replace (sp0 - 136) with (sp0 - 144 + 8) by lia; apply (F 8 (pi_shx 19 32));
    [cbn; tauto | apply pil_shx_denot; [exact E19 | exact E32 | lia | lia | lia] | apply Hsh; lia]|].
  split; [replace (sp0 - 128) with (sp0 - 144 + 16) by lia; apply (F 16 (SOff 19 32));
    [cbn; tauto | apply bv_eq; rewrite denot_SOff, E19, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia | lia]|].
  split; [replace (sp0 - 120) with (sp0 - 144 + 24) by lia; apply (F 24 (pi_shx 19 24));
    [cbn; tauto | apply pil_shx_denot; [exact E19 | exact E32 | lia | lia | lia] | apply Hsh; lia]|].
  replace (sp0 - 112) with (sp0 - 144 + 32) by lia; apply (F 32 (SOff 19 24));
    [cbn; tauto | apply bv_eq; rewrite denot_SOff, E19, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia | lia].
Qed.

(* ================= a segment's start state ================= *)
(* a literal text window at the cursor is apart from the resume regions (frame, the shadow-base cells, q, v) *)
Lemma pil_treg_disj : forall E bs cs pc,
  bv_unsigned (ew E (xatom 0)) = pc -> bv_unsigned (ew E 2) = sp0 - 144 -> bv_unsigned (ew E 9) = q ->
  bv_unsigned (ew E 19) = v ->
  text <= pc -> pc + Z.of_nat (length bs) <= text + len -> len < tcap -> text + tcap <= alloc_ceiling ->
  4096 + HEAD <= text -> (text + tcap <= 0x10000 \/ FS_IMG_END <= text - HEAD) ->
  all_disjoint E (pik_treg (xatom 0) 0 bs) (fsT_ret_regions 144 cs pib_rs).
Proof.
intros E bs cs pc E0 E2 E9 E19 H1 H2 H3 H4 H5 Himg.
pose proof pil_q_stack as (_ & _ & _ & Hqc & Hq47). pose proof pil_sp0 as (_ & HceilS & _). pose proof pil_stk144.
pose proof pil_v_rng as (Hv1 & Hv2).
apply all_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR, pik_treg,
  extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E0, E2, E9, E19.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
  HEAD in *.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; try exact I; destruct HVTX; lia.
Qed.
(* the narrowed region list is a submemory of the resume state's (with the extra regions in front) *)
Lemma pil_subregion_refl : forall rg, YP06.subregion rg rg.
Proof.
intros rg. unfold YP06.subregion. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [right; lia | intros c Hc; exact Hc].
Qed.
Lemma pil_submem : forall ex cs fw qw vw,
  (snd fw <= fst fw \/ 0 <= fst fw /\ snd fw <= 144) -> (snd qw <= fst qw \/ 0 <= fst qw /\ snd qw <= 24) ->
  (snd vw <= fst vw \/ 0 <= fst vw /\ snd vw <= 56) ->
  YP06.submem (ex ++ pib_rgs cs fw qw vw) (ex ++ fsT_ret_regions 144 cs pib_rs).
Proof.
intros ex cs fw qw vw Hf Hq Hv. induction ex as [|r ex IH]; cbn [app].
- unfold pib_rgs, fsT_ret_regions, pib_rs. cbn [app].
  apply YP06.submem_keep; [unfold YP06.subregion, fstk_ret; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi
    YP09.r_chunks]; split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia | intros c Hc; exact Hc]|].
  apply YP06.submem_keep; [apply pil_subregion_refl|].
  apply YP06.submem_keep; [apply pil_subregion_refl|].
  apply YP06.submem_keep; [unfold YP06.subregion, pi_qR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi
    YP09.r_chunks]; split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia | intros c Hc; exact Hc]|].
  apply YP06.submem_keep; [unfold YP06.subregion, pib_vR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi
    YP09.r_chunks]; split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia | intros c Hc; exact Hc]|].
  apply YP06.submem_nil.
- apply YP06.submem_keep; [apply pil_subregion_refl | exact IH].
Qed.
(* the kit's resume state, callee-saved registers restated, the extra regions added (each apart from the resume
   regions and from each other), the facts added, then narrowed to the segment's windows: pib_start *)
Lemma pil_start : forall regs' xs (W' : world tfibsegs) memX r cs gf R' ex atl cds al fw qw vw,
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r 144 cs pib_rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) memX (seg_rom tfibsegs))) ->
  Forall (fun r => fst r <> 0%bv /\ YK11.getr regs' (fst r) = sv_denot (Ereg regs' (fs_extraT ++ xs)) (snd r)) R' ->
  regions_wf (ex ++ fsT_ret_regions 144 cs pib_rs) = true ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' memX)) ex ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (ex ++ fsT_ret_regions 144 cs pib_rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) atl -> conds_ok (Ereg regs' (fs_extraT ++ xs)) cds ->
  alias_ok (Ereg regs' (fs_extraT ++ xs)) al ->
  (snd fw <= fst fw \/ 0 <= fst fw /\ snd fw <= 144) -> (snd qw <= fst qw \/ 0 <= fst qw /\ snd qw <= 24) ->
  (snd vw <= fst vw \/ 0 <= fst vw /\ snd vw <= 56) ->
  regions_wf (ex ++ pib_rgs cs fw qw vw) = true ->
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (pib_start r cs gf (pib_rgs cs fw qw vw) R' ex atl cds al)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) memX (seg_rom tfibsegs))).
Proof.
intros regs' xs W' memX r cs gf R' ex atl cds al fw qw vw HS HR' Hwf RX DJ HA HC HL Hf Hq Hv Hwf2.
assert (H1 : st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs))
  (pik_addf (pik_addr (pik_setr (fss_retT r 144 cs pib_rs gf) R') ex) atl cds al)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) memX (seg_rom tfibsegs)))).
{ apply pik_st_ok_addf; [| exact HA | exact HC | exact HL].
  apply pik_st_ok_addr; [| exact Hwf | rewrite restrict_mem; exact RX | exact DJ].
  apply pik_st_ok_setr; [exact HS|]. cbn [ms_regs mkst restrict]. exact HR'. }
pose proof (pik_st_ok_setm _ _ _ (ex ++ pib_rgs cs fw qw vw) H1 (pil_submem ex cs fw qw vw Hf Hq Hv) Hwf2) as H2.
exact H2.
Qed.

(* ================= the members' own facts (FS_DOC_STRS, well-formedness, depth) ================= *)
Lemma pil_mem_facts_gen : forall d l, FSDocStrs.fs_doc_values (PjTree.JObj l) -> FSDocStrs.fs_doc_strings (PjTree.JObj l) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj l) -> (PjTree.depth (PjTree.JObj l) <= Datatypes.S d)%nat ->
  forall dn kk x rm, l = dn ++ (kk, x) :: rm ->
  plain_bytes kk /\ (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_strings x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\ (PjTree.depth x <= d)%nat.
Proof.
intros d l HV HS HF HD dn. revert l HV HS HF HD.
induction dn as [|[k0 x0] dn IH]; intros l HV HS HF HD kk x rm El; subst l; cbn [app] in *.
- destruct (pim_vals_cons kk x rm HV) as (V1 & _). destruct (pim_strs_cons kk x rm HS) as (S1 & S2 & _).
  destruct (pim_wf_cons kk x rm HF) as (F1 & _). destruct (pim_depth_cons kk x rm d HD) as (D1 & _).
  repeat split; assumption.
- destruct (pim_vals_cons k0 x0 _ HV) as (_ & V2). destruct (pim_strs_cons k0 x0 _ HS) as (_ & _ & S3).
  destruct (pim_wf_cons k0 x0 _ HF) as (_ & F2). destruct (pim_depth_cons k0 x0 _ d HD) as (_ & D2).
  exact (IH _ V2 S3 F2 D2 kk x rm eq_refl).
Qed.
Lemma pil_mem_facts : forall dn kk x rm, ms = dn ++ (kk, x) :: rm ->
  plain_bytes kk /\ (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_strings x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\
  (PjTree.depth x <= 2 - Datatypes.S k)%nat.
Proof.
intros dn kk x rm E. apply (pil_mem_facts_gen (1 - k) ms HDV HDS HWF ltac:(lia) dn kk x rm E).
Qed.

(* ================= the frame chain at q across a memory change off [q, q + 24) ================= *)
Lemma pil_fpchain_kept : forall (l1 l2 : Z -> option Z) top cl bp,
  fpchain l1 bp top cl -> (bp = q \/ q + 40 <= bp) -> sp0 + 16 <= bp ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ q + 40 <= snd r) cl ->
  (forall a, sp0 <= a -> a + 8 <= q \/ q + 24 <= a -> l2 a = l1 a) -> fpchain l2 bp top cl.
Proof.
intros l1 l2 top cl. induction cl as [|[[fp ra] nfp] cl IH]; intros bp H Hb Hs HF Hl; cbn [fpchain] in *.
- destruct H as (r & Hr & Hr2). exists r. rewrite Hl by lia. split; assumption.
- destruct H as (E & H8 & Hra & Hnfp & H4 & Hrest). subst fp.
  inversion HF as [|? ? Hr HF']; subst. cbn [fst snd] in Hr.
  split; [reflexivity|]. split; [exact H8|]. split; [rewrite Hl by lia; exact Hra|].
  split; [rewrite Hl by lia; exact Hnfp|]. split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  assert (Hn : bp < nfp) by (unfold bad_next in Eb; apply orb_false_iff in Eb as [Eb _];
                             apply orb_false_iff in Eb as [Eb _]; apply Z.leb_gt in Eb; exact Eb).
  apply (IH nfp Hrest); [| lia | exact HF' | exact Hl].
  destruct Hr as [Hr | Hr]; [exfalso; congruence | right; exact Hr].
Qed.
Lemma pil_chain_kept : forall ly1 ly2 (rd1 rd2 : reader) chq,
  achain ly1 rd1 sp0 q chq -> Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq ->
  ly_top ly1 = ly_top ly -> ly_top ly2 = ly_top ly ->
  (forall a, sp0 <= a -> ~ (q <= a < q + 24) -> rd2 a = rd1 a) -> achain ly2 rd2 sp0 q chq.
Proof.
intros ly1 ly2 rd1 rd2 chq H HF E1 E2 Hrd. unfold achain in *. rewrite E2. rewrite E1 in H.
destruct H as [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H|]. right.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
apply (pil_fpchain_kept (rdword rd1) (rdword rd2) (ly_top ly) chq q H4 (or_introl eq_refl) H1 HF).
intros a Ha Hout. apply rdword_ext. intros j Hj. apply Hrd; lia.
Qed.
Lemma pil_wkeep_trans : forall (W1 W2 : world tfibsegs) m1 m2 s,
  wkeep tfibsegs W W1 mem m1 sp0 ot q 24 -> wkeep tfibsegs W1 W2 m1 m2 s ot q 24 -> s <= sp0 ->
  wkeep tfibsegs W W2 mem m2 sp0 ot q 24.
Proof.
intros W1 W2 m1 m2 s H1 H2 Hs a Ha Hq.
destruct (H1 a Ha Hq) as (B1 & R1). destruct (H2 a ltac:(lia) Hq) as (B2 & R2).
split; [rewrite B2; exact B1 | rewrite R1; exact R2].
Qed.
Lemma pil_frames : forall lyc Sc Uc (W1 : world tfibsegs) memC mdC kc, JC lyc Sc Uc W1 memC mdC kc -> frames Sc = frames S.
Proof.
intros lyc Sc Uc W1 memC mdC kc (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
End L.
