(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjLeaves SjStage1 SjStage1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_tables Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs El_defs El_hdr El_h2 El_h3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition EJT_TAB : list Z :=
  [164376; 164648; 164568; 164776; 164788; 164608; 164664; 164676; 164812; 164800; 164480; 164624; 164532; 164432; 164688; 164708;
   164836; 164824; 164404; 164552; 164848; 164416; 164516; 164468; 164636; 164444; 164884; 164264; 164864; 164492; 164584; 164732].
Definition ejt (i : Z) : Z := nth (Z.to_nat i) EJT_TAB 0.
Definition EJT_WORDS : list word := map (Z_to_bv 64) EJT_TAB.

Lemma ejt_image : ro_bytes_b usegs EL_JTAB (u32s EJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ejt_at : forall m, mem_inv usegs m -> bytes_at usegs m EL_JTAB (u32s EJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EL_JTAB; lia | rewrite u32s_length; unfold EL_JTAB, EJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact ejt_image.
Qed.
Lemma ejt_read : forall (m : word -> option byte) i a, mem_inv usegs m -> 0 <= i < 32 -> a = wa (EL_JTAB + 4 * i) ->
  ov_read_bytes usegs m a 4 = Some (le4 (Z_to_bv 64 (ejt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EL_JTAB EJT_WORDS i); [apply ejt_at; exact MI| | lia | reflexivity].
  unfold EJT_WORDS, ejt. rewrite nth_error_map. rewrite (nth_error_nth' EJT_TAB 0); [reflexivity|].
  change (length EJT_TAB) with 32%nat. lia.
Qed.
Lemma ejt_range : forall i, 0 <= i < 32 -> 0 <= ejt i < 2 ^ 31.
Proof.
  intros i Hi. unfold ejt.
  assert (F : forallb (fun x => (0 <=? x) && (x <? 2 ^ 31)) EJT_TAB = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. assert (L : (Z.to_nat i < length EJT_TAB)%nat) by (change (length EJT_TAB) with 32%nat; lia).
  specialize (F _ (nth_In EJT_TAB 0 L)). apply andb_true_iff in F. destruct F as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2. lia.
Qed.

Definition EL_ARMS : list Z :=
  [0x3c2e0; 0x3c3f0; 0x3c3a0; 0x3c470; 0x3c47c; 0x3c3c8; 0x3c400; 0x3c40c; 0x3c494; 0x3c488; 0x3c348; 0x3c3d8; 0x3c37c; 0x3c318; 0x3c418; 0x3c42c;
   0x3c4ac; 0x3c4a0; 0x3c2fc; 0x3c390; 0x3c4b8; 0x3c308; 0x3c36c; 0x3c33c; 0x3c3e4; 0x3c324; 0x3c4dc; EL_EXIT; 0x3c4c8; 0x3c354; 0x3c3b0; 0x3c444].
Definition el_target (a : Z) : Z := nth (Z.to_nat a) EL_ARMS EL_EXIT.

Lemma ejt_target : forall a, 0 <= a <= 31 -> EL_JTAB + ejt a = el_target a.
Proof.
  intros a Ha.
  assert (F : forallb (fun i => EL_JTAB + ejt i =? el_target i) (map Z.of_nat (seq 0 32)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in F. apply Z.eqb_eq. apply F.
  apply in_map_iff. exists (Z.to_nat a). split; [lia|]. apply in_seq. lia.
Qed.

Definition el_live (a : Z) : bool :=
  (a =? 8) || (a =? 22) || (a =? 23) || (a =? 24) || (a =? 25) || (a =? 26) || (a =? 28) || (a =? 29) || (a =? 30) || (a =? 31).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma el_act_dead : forall a d, el_action d = a -> 0 <= a < 32 -> el_live a = false -> el_act lops d = mret tt.
Proof.
  intros a d EA Ha H. unfold el_act, el_throwing. rewrite EA. unfold el_live in H.
  repeat (apply orb_false_iff in H; destruct H as [H ?]).
  repeat match goal with H' : (a =? ?v) = false |- _ => rewrite H'; clear H' end. cbn [orb]. reflexivity.
Qed.

Definition act_env (E : aenv) (m0 m : mem) (s00 st : PState) (LB : list block) (D : Z) (d : list Z) (sp0 lo B : Z) (errv : word)
    (bvp psb ptp pim pix poc pia : bptr) (A cap IMPL IDX OC IA : Z) (jr : list byte)
    (j0 jres jos j313 j329 j361 j416 j441 : list byte) (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (fc : bv 32) : Prop :=
  aenv_ok E /\ AINV E m /\
  ae_LB E = el_blocks psb ptp pim pix poc pia bvp IA OC IDX IMPL (ae_TAPE E) (ae_SBUF E) A cap (doc_cap d) LB /\ ae_lo E = lo /\ ae_B E = B /\ ae_DOC E = sp0 + 336 /\ ae_p1 E = el_str d /\
  RHEAP s00 LB m0 /\ lx_statics m0 /\
  RHEAP st (ae_LB E) m /\ rauxv_ok m B /\ sp0 + 528 <= B /\ B < 2^62 /\
  stk usegs m lo sp0 /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo /\ lo <= sp0 + 528 - LX_FUZZ_STACK /\
  rw_cells usegs m LX_ERRNO [C4 errv] /\ mem_inv usegs m /\ (sp0 + 528) mod 16 = 0 /\ frm0 fc /\
  lx_pres LB (sp0 + 528) [LXW_SJ; LXW_UNW] m0 m /\ sj_statics m true /\ payload_ok m LB D d /\ el_fd_ok d = true /\
  vrep m (sp0 + 392) A (cap, Z.of_nat (el_P d), Some bvp) (el_els D d) jr /\ nth 0 (el_els D d) (0, 0) = (ae_PTR E, zlength (el_str d)) /\
  rw_cells usegs m sp0 [CB 8 j0] /\ rw_cells usegs m (sp0 + 8) [CB 24 jres] /\ rw_cells usegs m (sp0 + 32) [CB 264 jos] /\
  el_root E m (sp0 + 296) /\
  rw_cells usegs m (sp0 + 312) [C1 (Z_to_bv 8 0); CB 7 j313] /\ rw_cells usegs m (sp0 + 320) [C8 (Z_to_bv 64 IMPL)] /\
  rw_cells usegs m (sp0 + 328) [C1 (Z_to_bv 8 0); CB 3 j329; C4 (Z_to_bv 64 12)] /\ rw_cells usegs m (sp0 + 352) [C8 (Z_to_bv 64 (doc_cap d))] /\
  rw_cells usegs m (sp0 + 360) (p48_cells (Z_to_bv 8 0) j361 (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
  rw_cells usegs m IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv) /\
  rw_cells usegs m (sp0 + 416) [CB 4 j416; C4 (Z_to_bv 64 (el_sel d))] /\
  rw_cells usegs m (sp0 + 424) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j441] /\
  rw_cells usegs m (sp0 + 448) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition arm_stmt (a pc : Z) : Prop :=
  forall (R : Type) (k : unit -> M PState R) (Q : R -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 xs0 ya0 ya1 a2 a3 a4 a5 a6 a7 xs3 xs4 xs5 ys6 xs8 s9 s10 s11 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : mem) (s00 st : PState) (LB : list block) (D : Z) (d : list Z) (sp0 lo B : Z) (E : aenv) (errv : word)
    (bvp psb ptp pim pix poc pia : bptr) (A cap IMPL IDX OC IA : Z) (jr : list byte)
    (j0 jres jos j313 j329 j361 j416 j441 : list byte) (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
  el_action d = a ->
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  (forall st' ms', act_post sp0 gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra st (ae_LB E) LB lo B D d m0 A cap (el_P d) IMPL IDX OC IA (ae_TAPE E) (ae_SBUF E) (Z_to_bv 64 (doc_cap d)) st' ms' ->
      implM usegs (k tt) st' Q ms') ->
  implM usegs (mbind (el_act lops d) k) st Q
    (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 (Z_to_bv 64 (zlength (el_str d))) ya0 ya1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (ae_PTR E)) xs3 xs4 xs5 ys6 (Z_to_bv 64 0xFFFFFFC0) xs8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Lemma act_post_here : forall E m0 m s00 st st' LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc
    (x1 gp t0 t1 t2 y8 y9 y10 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 t3 t4 t5 t6 : word) F,
  act_env E m0 m s00 st' LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc -> ps_fa st' = ps_fa st -> ps_so st' = ps_so st ->
  act_post sp0 gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra st (ae_LB E) LB lo B D d m0 A cap (el_P d) IMPL IDX OC IA (ae_TAPE E) (ae_SBUF E) (Z_to_bv 64 (doc_cap d)) st'
    (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 y8 y9 y10 a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EL_EXIT) fc None m (seg_rom usegs)).
Proof.
  intros until F. intros AE FAQ SOQ.
  destruct AE as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                  & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  destruct AI as (TAPEB & SBUFB & PTRB & DOCC). rewrite EDOC in DOCC. unfold el_root in ROOT. rewrite EDOC in ROOT.
  destruct VR as (ELS & SZ & SV & BLK).
  pose proof (rw_cells_join _ _ _ _ _ J0 RES ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
  pose proof (rw_cells_join _ _ _ _ _ J1 OS ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
  pose proof (rw_cells_join _ _ _ _ _ J2 ROOT ltac:(cbn [app cells_size csize Nat.add]; lia)) as J3. cbn [app] in J3.
  destruct (rw_cells_forget _ _ _ _ J3) as [jlo LOW]. cbn [cells_size csize Nat.add] in LOW.
  destruct (rw_cells_forget _ _ _ _ XSEL) as [jsel XSEL']. cbn [cells_size csize Nat.add] in XSEL'.
  pose proof (rw_cells_join _ _ _ _ _ XSEL' XFD ltac:(cbn [cells_size csize Nat.add]; lia)) as J5. cbn [app] in J5.
  destruct (rw_cells_forget _ _ _ _ J5) as [jmid MID]. cbn [cells_size csize Nat.add] in MID.
  pose proof (rw_cells_join _ _ _ _ _ DOCC DCAP ltac:(cbn [cells_size csize Nat.add]; lia)) as DOC3. cbn [app] in DOC3.

  pose proof (tp_of_pres _ _ _ _ LXS0 PRES) as TPC. apply pres_X3 in PRES.
  unfold act_post. do 25 eexists. exists F, fc, m, errv, true. exists nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50, j313, j329, j361, jlo, jmid.
  split; [reflexivity|].
  repeat (split; [first [assumption | reflexivity]|]). exact SAVE.
Qed.

Lemma act_env_fc : forall E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc fc',
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc -> frm0 fc' ->
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc'.
Proof.
  intros until fc'. intros AE FRM'.
  destruct AE as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & REST).
  repeat (split; [assumption|]). exact REST.
Qed.

Lemma act_env_call : forall E m0 m m' s00 st st' LB D d sp0 lo B errv errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos jres' jos' j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc fc',
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  munch [(lo, sp0); (sp0 + 8, sp0 + 296)]%Z m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' lo sp0 ->
  RHEAP st' (ae_LB E) m' -> ps_fa st' = ps_fa st -> ps_so st' = ps_so st -> rw_cells usegs m' LX_ERRNO [C4 errv'] ->
  rw_cells usegs m' (sp0 + 8) [CB 24 jres'] -> rw_cells usegs m' (sp0 + 32) [CB 264 jos'] -> frm0 fc' ->
  act_env E m0 m' s00 st' LB D d sp0 lo B errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres' jos' j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc'
  /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st.
Proof.
  intros until fc'. intros AE MU WM MI' ST' HEAP' FA' SO' ERR' RES' OS' FRM'.
  destruct AE as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                  & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (BLA : forall a, in_block (ae_LB E) a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
  pose proof (LH_block_range _ _ _ _ HEAP ltac:(rewrite ELB; do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & _).
  pose proof (LH_block_range _ _ _ _ HEAP ltac:(rewrite ELB; do 6 right; left; reflexivity)) as (A0 & _ & _ & AC & _).
  cbn [blk_addr blk_size fst snd] in IM0, IMC, A0, AC. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in IMC, AC.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  Ltac hi_frame AG H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; try unfold p48_cells, impl_cells16, el_root in Ha; cbn in Ha; cbn [outside]; lia].
  hi_frame AG J0. hi_frame AG PA0. hi_frame AG PIMPL. hi_frame AG PA16. hi_frame AG DCAP. hi_frame AG P48. hi_frame AG XSEL. hi_frame AG XFD. hi_frame AG SAVE.
  unfold el_root in ROOT. hi_frame AG ROOT.
  apply (rw_cells_agree _ _ _ _ _ AG) in THIS; [| intros a Ha; unfold impl_cells16 in Ha; cbn in Ha; cbn [outside]; clear - Ha IMC CEIL LO; lia].
  destruct VR as (ELS & SZ & SV & BLK). hi_frame AG SV.
  apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO; lia| exact ELS| lia].
  split; [| split; assumption].
  split; [exact OK|]. split.
  { eapply AINV_agree; [exact AI| exact AG| | | exact OK].
    - intros a Ha. specialize (BLA a Ha). cbn [outside]. lia.
    - intros a Ha. rewrite EDOC in Ha. cbn [outside]. lia. }
  do 7 (split; [assumption|]). split; [exact HEAP'|]. split.
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  do 6 (split; [assumption|]). split; [exact ERR'|]. split; [exact MI'|]. split; [exact AL16|]. split; [exact FRM'|]. split.
  { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [outside]. destruct HC as [HC|[HC|HC]]; [| specialize (BLB a HC)|]; (split; [lia| split; [lia| exact I]]). }
  split. { eapply sj_statics_agree; [exact AG| | exact SJS]. intros a Ha. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [outside]. lia. }
  split. { eapply payload_ok_agree; [exact AG| exact PL|]. intros b a Hb Ha. assert (BA : a < alloc_ceiling) by (apply BLB; exists b; auto). cbn [outside]. lia. }
  split; [exact FD|]. split; [split; [exact ELS| split; [exact SZ| split; [exact SV| exact BLK]]]|]. split; [exact NTH0|].
  split; [exact J0|]. split; [exact RES'|]. split; [exact OS'|]. split; [exact ROOT|].
  repeat (split; [assumption|]). exact SAVE.
Qed.

Lemma act_env_pres : forall E m0 m m' s00 st st' LB D d sp0 lo B errv errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos jres' j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc fc',
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  lx_pres (ae_LB E) sp0 [(sp0 + 8, sp0 + 32)]%Z m m' -> mem_inv usegs m' -> stk usegs m' lo sp0 ->
  RHEAP st' (ae_LB E) m' -> ps_fa st' = ps_fa st -> ps_so st' = ps_so st -> rw_cells usegs m' LX_ERRNO [C4 errv'] -> rauxv_ok m' B ->
  rw_cells usegs m' (sp0 + 8) [CB 24 jres'] -> frm0 fc' ->
  act_env E m0 m' s00 st' LB D d sp0 lo B errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres' jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc'
  /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st.
Proof.
  intros until fc'. intros AE PRES' MI' ST' HEAP' FA' SO' ERR' AUX' RES' FRM'.
  destruct AE as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                  & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (INB : forall b a, In b (ae_LB E) -> blk_addr b <= a < blk_addr b + blk_size b -> lx_client (ae_LB E) sp0 [(sp0 + 8, sp0 + 32)] a).
  { intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC.
    split; [cbn [rin_ivs fst snd]; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
  assert (LBsub : forall b, In b LB -> In b (ae_LB E)) by (intros b Hb; rewrite ELB; unfold el_blocks; do 7 right; exact Hb).
  pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
  assert (FRCL : forall a, sp0 <= a < sp0 + 528 -> ~ (sp0 + 8 <= a < sp0 + 32) -> lx_client (ae_LB E) sp0 [(sp0 + 8, sp0 + 32)] a).
  { intros a Ha N1. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
  Ltac hi_frame2 AG FRCL H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; try unfold p48_cells, el_root in Ha; cbn in Ha; apply FRCL; lia].
  hi_frame2 AG FRCL J0. hi_frame2 AG FRCL OS. hi_frame2 AG FRCL PA0. hi_frame2 AG FRCL PIMPL. hi_frame2 AG FRCL PA16. hi_frame2 AG FRCL DCAP. hi_frame2 AG FRCL P48.
  hi_frame2 AG FRCL XSEL. hi_frame2 AG FRCL XFD. hi_frame2 AG FRCL SAVE.
  unfold el_root in ROOT. hi_frame2 AG FRCL ROOT.
  apply (rw_cells_agree _ _ _ _ _ AG) in THIS; [| intros a Ha; eapply INB; [rewrite ELB; unfold el_blocks; do 3 right; left; reflexivity| unfold impl_cells16 in Ha; cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
  destruct VR as (ELS & SZ & SV & BLK). hi_frame2 AG FRCL SV.
  apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK; [| intros a _ Ha; eapply INB; [rewrite ELB; unfold el_blocks; do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
  split; [| split; assumption].
  split; [exact OK|]. split.
  { eapply AINV_agree; [exact AI| exact AG| | | exact OK].
    - intros a (b & Hb & Hr). eapply INB; [exact Hb| exact Hr].
    - intros a Ha. rewrite EDOC in Ha. apply FRCL; lia. }
  do 7 (split; [assumption|]). split; [exact HEAP'|]. split; [exact AUX'|].
  do 6 (split; [assumption|]). split; [exact ERR'|]. split; [exact MI'|]. split; [exact AL16|]. split; [exact FRM'|]. split.
  { eapply lx_pres_trans; [exact PRES|]. eapply (lx_pres_sub LB (sp0 + 528) _ _ _ _ _ _ PRES'); [lia| exact LBsub|].
    intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB a IB); lia| lia]. }
  split. { eapply sj_statics_agree; [exact AG| | exact SJS]. intros a Ha. apply sjs_addr_client; [exact Ha|]. pose proof (sjs_addr_lt a Ha) as [R1 _]. unfold GLOBALS_TOP in R1. cbn [rin_ivs fst snd]. lia. }
  split. { eapply payload_ok_agree; [exact AG| exact PL|]. intros b a Hb Ha. eapply INB; [apply LBsub; exact Hb| exact Ha]. }
  split; [exact FD|]. split; [split; [exact ELS| split; [exact SZ| split; [exact SV| exact BLK]]]|]. split; [exact NTH0|].
  split; [exact J0|]. split; [exact RES'|]. split; [exact OS|]. split; [exact ROOT|].
  repeat (split; [assumption|]). exact SAVE.
Qed.

Definition throw_slot (SITE D RA : Z) (XP : mem -> Z -> Prop) (XR : Z -> word -> Prop) : Prop :=
  forall (R : Type) (k : unit -> M PState R) (Q : R -> PState -> machine_state -> Prop)
    (x1 gp t0 t1 t2 xs0 xs1 ya0 ya1 ya2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6 : word) (jx : list byte) (s0 s1 s2 s3 s4 s5 s6 s7 s8 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m m1 : mem) (s00 st : PState) (LB : list block) (D0 : Z) (d : list Z) (sp0 lo B : Z) (E : aenv) (errv : word)
    (bvp psb ptp pim pix poc pia : bptr) (A cap IMPL IDX OC IA : Z) (jr : list byte)
    (j0 jres jos j313 j329 j361 j416 j441 : list byte) (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
  act_env E m0 m s00 st LB D0 d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  munch [(lo, sp0)]%Z m m1 -> wmono usegs m m1 -> mem_inv usegs m1 -> stk usegs m1 lo (sp0 + -16) ->
  rw_cells usegs m1 (sp0 + -16) [CB 8 jx; C8 (Z_to_bv 64 RA)] -> XP m1 (sp0 + -16) -> XR (sp0 + -16) xs1 ->
  (forall st' ms', act_post sp0 gp s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra st (ae_LB E) LB lo B D0 d m0 A cap (el_P d) IMPL IDX OC IA (ae_TAPE E) (ae_SBUF E) (Z_to_bv 64 (doc_cap d)) st' ms' ->
      implM usegs (k tt) st' Q ms') ->
  implM usegs (mbind (newnt lops EL_EXC) (fun e => mbind (del lops e) k)) st Q
    (MS (mkR x1 (Z_to_bv 64 (sp0 - 16 - D)) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 ya0 ya1 ya2 a3 a4 a5 a6 a7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE) fc None m1 (seg_rom usegs)).

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Lemma act_cases : forall a, 0 <= a < 32 ->
  a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15 \/
  a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 27 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31.
Proof. intros a H. lia. Qed.

Section Proofs.
  Hypothesis ARMS : forall a, 0 <= a < 32 -> a <> 27 -> arm_stmt a (el_target a).

  Theorem el_act_of_arms : el_act_stmt.
  Proof.
    unfold el_act_stmt. intros until p50.
    intros OK AI ELB ELO EB EDOC EP1 HEAP00 LXS0 HEAP AUX QB B63 ST CEIL GLO LO ERR MI AL16 FRM PRES SJS PL FD VR NTH0 J0 RES OS ROOT PA0 PIMPL PA16 DCAP P48 THIS XSEL XFD SAVE HK.
    assert (AE : act_env E m0 m s00 st LB D d sp0 lo B errv bv psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
                         s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc) by (repeat (split; [assumption|]); assumption).
    unfold EL_DISPATCH, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof PL as (_ & PRNG & _). pose proof (el_action_range d PRNG) as AR.
    remember (el_action d) as a eqn:EA. symmetry in EA.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.

    zstep. zstep. if_cases KLT; zify_cond KLT; [exfalso; rewrite ?unsigned_lit in KLT by lia; lia|]. clear KLT.
    zstep. step. zstep. zstep.
    pose proof (ejt_range a ltac:(lia)) as EJR.
    pose proof (ejt_read m a (wa (Z.shiftl a 2 + 82120)) MI ltac:(lia) ltac:(unfold wa, EL_JTAB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RJ.
    zstep. zstep. rewrite (a_swrap32_small (ejt a)) by lia.
    replace (ejt a + 82120) with (el_target a) by (rewrite <- ejt_target by lia; unfold EL_JTAB; lia).
    Ltac exit27 EA AE HK :=
      lazymatch goal with |- context [el_target 27] =>
        change (el_target 27) with 0x3c270; zstep; ihere; to_implM;
        rewrite (el_act_dead 27 _ EA ltac:(lia) eq_refl);
        apply implM_ret_bind; apply HK; eapply act_post_here; [exact AE| reflexivity| reflexivity] end.
    Ltac go_arm ARMS EA AE HK :=
      lazymatch goal with |- context [el_target ?v] =>
        let t := eval vm_compute in (el_target v) in
        change (el_target v) with t; zstep; ihere; to_implM;
        eapply (ARMS v ltac:(lia) ltac:(lia)); [exact EA| exact AE| exact HK] end.
    pose proof (act_cases a AR) as CASES.
    repeat (destruct CASES as [-> | CASES]; [first [exit27 EA AE HK | go_arm ARMS EA AE HK] |]).
    rewrite CASES in *. go_arm ARMS EA AE HK.
  Qed.
End Proofs.
End WithCeiling0.
