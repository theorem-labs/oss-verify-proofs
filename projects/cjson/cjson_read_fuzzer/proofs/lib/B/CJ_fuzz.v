(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_delete.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PermFacts.
  Context {X : Type}.
  Implicit Types (x : X) (Bv Bk Bc Bn LR : list X).

  Lemma perm_node_nokids : forall x Bv Bk Bn LR,
    Permutation (x :: Bv ++ Bk ++ Bn ++ LR) ((x :: Bv ++ Bk ++ [] ++ Bn) ++ LR).
  Proof. intros. cbn [app]. rewrite <- !app_assoc. apply Permutation_refl. Qed.

  Lemma perm_node_kids : forall x Bv Bk Bc Bn LR,
    Permutation (Bc ++ x :: Bv ++ Bk ++ Bn ++ LR) ((x :: Bv ++ Bk ++ Bc ++ Bn) ++ LR).
  Proof.
    intros. cbn [app]. rewrite <- !app_assoc. apply Permutation_sym.
    apply (@Permutation_cons_app X (Bv ++ Bk ++ Bc ++ Bn ++ LR) Bc (Bv ++ Bk ++ Bn ++ LR) x).
    rewrite (app_assoc Bv Bk (Bc ++ Bn ++ LR)), (app_assoc Bv Bk (Bn ++ LR)).
    apply Permutation_sym, Permutation_app_swap_app.
  Qed.
End PermFacts.

(* [comment removed for export] *)
Lemma shadow_ok_shb0 : forall m A n a,
  shadow_ok m A n -> A <= a -> a + 8 <= A + n -> a mod 8 = 0 -> shb m a 0.
Proof.
  intros m A n a SO H1 H2 AL.
  destruct (shadow_ok_shchk m A n a 8 SO H1 H2 ltac:(lia) AL) as (v & SHB & [->|[C1 C2]]); [exact SHB|].
  exfalso. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, AMALLOC_STACK in *; lia.

(* [comment removed for export] *)
Lemma le4_wz_small : forall ty, 0 <= ty < 256 -> le4 (wz ty) = [wb ty; wb 0; wb 0; wb 0].
Proof.
  intros ty H. unfold le4, wz, wb. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  replace (Z.shiftr ty 8) with 0 by (rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_small by lia; reflexivity).
  reflexivity.
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Definition nodeB (nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z) : list cell :=
  [C8 (wz nx); C8 pv; C8 (wz ch); C1 (wb ty); C1 (wb 0); C1 (wb 0); C1 (wb 0); C4 p1; C8 (wz vs); C4 vi; C4 p2; C8 vd; C8 (wz ky)].

Lemma nodeB_of_node : forall m p nx pv ch ty p1 vs vi p2 vd ky, 0 <= ty < 256 ->
  rw_cells bsegs m p (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> rw_cells bsegs m p (nodeB nx pv ch ty p1 vs vi p2 vd ky).
Proof.
  intros until ky. intros TY H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I|].
  unfold nodeB, node_cells. cbn [cells_bytes cbytes app]. rewrite (le4_wz_small ty TY). reflexivity.
Qed.

Section StoreFacts.
  Variable AI : art_iface.
  (* [comment removed for export] *)
  Lemma cj_pres_block_store : forall sp0 SPB LBX LF TRS BB m0 mo g A n R LR SP lo' hi' m1 m2,
    ART AI sp0 SPB LBX LF TRS BB m0 mo g -> Permutation ((A, n) :: R) LBX -> (forall b, In b LR -> In b R) ->
    alloc_ceiling <= SP -> sp0 <= 2^47 ->
    munch [(lo', hi')] m1 m2 -> wmono bsegs m1 m2 -> A <= lo' -> hi' <= A + n ->
    cj_pres sp0 LR LF SP m1 m2.
  Proof.
    intros sp0 SPB LBX LF TRS BB m0 mo g A n R LR SP lo' hi' m1 m2 HL HP HLR HSP H47 MU WM Hlo Hhi a Ha Hc.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
    (* [comment removed for export] *)
    pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP))) as BND.
    pose proof alloc_ceiling_range as CR.
    try rewrite alloc_ceiling_eq in *. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in BND. bandM. sepM.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - destruct (lheap_perm_apart AI _ _ _ _ _ _ _ _ _ _ _ _ HL HP A' n' (HLR _ Hin)) as [_ D]. lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 8%nat; intros Hk _ HF1 HF2 _ _ _ HD).
      try rewrite alloc_ceiling_eq in HF2. unfold AIMG_HI in HF1.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      destruct (HD A n (perm_in_head _ _ _ HP)) as [D|D]; destruct BND as [BND|BND];
        unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; Z.div_mod_to_equations; lia.
    - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh.
      destruct BND as [BND|BND]; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cj_pres_stack_store : forall sp0 SPB LB LF TRS BB m0 mo g (L : list cblock) SP lo' hi' m1 m2,
    ART AI sp0 SPB LB LF TRS BB m0 mo g -> (forall b, In b L -> In b LB) ->
    munch [(lo', hi')] m1 m2 -> wmono bsegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP ->
    cj_pres sp0 L LF SP m1 m2.
  Proof.
    intros sp0 SPB LB LF TRS BB m0 mo g L SP lo' hi' m1 m2 HL HLB MU WM Hlo Hhi a Ha Hc.
    try rewrite alloc_ceiling_eq in Hlo.
    split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. cbn. split; [|exact I].
    destruct Hc as [Hs|[Hi|[(A' & n' & Hin & Hr)|[(Fr & k & Hin & Hr)|Hsh]]]].
    - lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (HLB _ Hin)) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4. lia.
    - (nelimp (art_frame_facts AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 5%nat; intros Hk _ HF1 HF2 _).
      try rewrite alloc_ceiling_eq in HF2.
      assert (fsz k = 128 \/ fsz k = 256) by (destruct Hk as [-> | ->]; [left| right]; reflexivity).
      unfold sclr, SH, SHADOW_OFFSET, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. Z.div_mod_to_equations. lia.
    - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
  Qed.
End StoreFacts.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).

  Section Loop.
    Variable dk : nat.
    Hypothesis REC : forall d, (d < dk)%nat -> delete_spec_at AI TI d.

    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m0 : word -> option byte) (g0 : lghost) (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np B0 : Z) (NB : nat)
              (lo : Z) (errv : word) (T : Z -> Prop).
    Hypothesis TP : tp = wz ATP.
    Hypothesis SPBle : bv_unsigned sp <= SPB.
    Hypothesis SP0 : sp0 <= 2^47.
    Hypothesis TOP : bv_unsigned sp + 16 < ASTACK_TOP sp0.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis BOT : ASTACK_BOTTOM sp0 <= lo.
    Hypothesis LO1 : lo <= bv_unsigned sp - 80 - AMALLOC_STACK.
    Hypothesis SPhi : bv_unsigned sp <= 2^64.
    Hypothesis SDEL : Forall (STAT TI) S_DELETE.
    Hypothesis BFIN : 0 <= B0 - cost_free * Z.of_nat NB.

    Notation SP1 := (bv_unsigned sp + -80).
    Notation BFINv := (B0 - cost_free * Z.of_nat NB).
    Notation POST := (delete_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B0 NB lo errv m0 g0).
    Notation FRAME mm fj := (rw_cells bsegs mm (bv_unsigned sp + -80) [CB 8 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

    (* [comment removed for export] *)
    Definition linv (LBX : list cblock) (TRSX : list (list Z)) (BX : Z) (m : word -> option byte) (mo : Model) (g : lghost) (fj : list byte) : Prop :=
      ART AI sp0 SPB LBX LF TRSX BX m mo g /\ stk bsegs m lo SP1 /\ FRAME m fj
      /\ rw_cells bsegs m AERRNO [C4 errv] /\ mem_inv bsegs m /\ cj_pres sp0 LR LF (bv_unsigned sp) m0 m
      /\ gmono g0 g /\ TINV TI np TRSX.

    (* [comment removed for export] *)
    Notation LST pc rav x5 x6 x7 nxt itm x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x28 x29 x30 x31 mm :=
      (MS (mkR rav (Z_to_bv 64 SP1) gp tp x5 x6 x7 itm nxt x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0xa5650) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

    (* [comment removed for export] *)
    Lemma st_item : STAT TI [PC0_FREE; 0x82664].
    Proof. exact (Forall_inv SDEL). Qed.
    Lemma st_vs : STAT TI [PC0_FREE; 0x82700].
    Proof. exact (Forall_inv (Forall_inv_tail SDEL)). Qed.
    Lemma st_key : STAT TI [PC0_FREE; 0x82744].
    Proof. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail SDEL))). Qed.

    (* [comment removed for export] *)
    Definition TestSpec (n : nat) : Prop :=
      forall (d : nat) (p : Z) (B LBX : list cblock) (TRSX : list (list Z)) (BX : Z) (m : word -> option byte) (mo : Model) (g : lghost) (fj : list byte)
             (rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 : word),
      (length B <= n)%nat -> (d <= dk)%nat ->
      lo <= bv_unsigned sp - DELETE_STACK d ->
      BX = BFINv + cost_free * Z.of_nat (length B) ->
      cj_chain T m d p B -> Permutation (B ++ LR) LBX -> linv LBX TRSX BX m mo g fj ->
      LSCPS bsegs POST (LST 0x82664 rav t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 m) mo g.

    Lemma SP1eq : bv_unsigned (Z_to_bv 64 SP1) = SP1.
    Proof. apply unsigned_lit. try rewrite alloc_ceiling_eq in CEIL. unfold AMALLOC_STACK in LO1. lia. Qed.

    (* [comment removed for export] *)
    Lemma SPtop : bv_unsigned sp + 16 <= sp0 + 4096.
    Proof. clear -TOP. unfold ASTACK_TOP, roundup in TOP. Z.div_mod_to_equations. lia. Qed.

    (* [comment removed for export] *)
    Lemma loop_exit : forall LBX TRSX m mo g fj rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6,
      Permutation LR LBX -> linv LBX TRSX BFINv m mo g fj ->
      LSCPS bsegs POST (LST 0x82664 rav t0 t1 t2 (Z_to_bv 64 0) s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 m) mo g.
    Proof.
      intros until t6. intros HP nelH_; (nelim nelH_ 8%nat; intros HL ST FR ERR MI PR GM TV).
      try rewrite alloc_ceiling_eq in CEIL. unfold AMALLOC_STACK in LO1.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      do 11 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply lscps_done. unfold delete_post.
      nexists 18%nat. split; [reflexivity|].
      split; [exact MI|]. split; [exact ST|]. split; [exact ERR|].
      split; [eapply (art_perm AI); [exact HL| apply Permutation_sym; exact HP| apply Permutation_refl]|].
      split; [apply Permutation_refl|]. split; [exact TV|]. split; [exact GM| exact PR].
    Qed.

    Section Body.
      Variable n : nat.
      Hypothesis IHn : forall n', (n' < n)%nat -> TestSpec n'.
      (* [comment removed for export] *)
      Variables (d0 : nat) (p nx : Z) (pv : word) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word) (ky : Z)
                (Bv Bk Bc Bn : list cblock).
      Hypothesis Dle : (S d0 <= dk)%nat.
      Hypothesis LOd : lo <= bv_unsigned sp - DELETE_STACK (S d0).
      Hypothesis LEN : (length ((p, 64%Z) :: Bv ++ Bk ++ Bc ++ Bn) <= n)%nat.
      Hypothesis PNZ : p <> 0.
      Hypothesis TY : 0 <= ty < 256.

      (* [comment removed for export] *)
      Lemma tail3 : forall LBX TRSX BX m mo g fj rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6,
        Permutation ((p, 64) :: Bn ++ LR) LBX -> linv LBX TRSX BX m mo g fj ->
        BX = BFINv + cost_free * Z.of_nat (length ((p, 64) :: Bn)) ->
        cj_chain T m (S d0) nx Bn ->
        LSCPS bsegs POST (LST 0x82658 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 m) mo g.
      Proof.
        intros until t6. intros HP (HL & ST & FR & ERR & MI & PR & GM & TV) HBX CHN.
        try rewrite alloc_ceiling_eq in CEIL. unfold AMALLOC_STACK in LO1. pose proof SP1eq as E1. pose proof SPtop as SPT.
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
        try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros CR1 CR2 CR3).
        (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros HK _ _ _). unfold AHOOKS in HK.
        lazymatch type of HK with cells_at _ ?mm ?a ?cs => change (ro_cells bsegs mm a cs) in HK end.
        assert (BXge : cost_free <= BX) by (rewrite HBX; cbn [length]; rewrite ?Nat2Z.inj_succ; rewrite cost_free_eq in *; lia).
        assert (NXS : nx <= bv_unsigned sp + -80).
        { destruct (Z.eq_dec nx 0) as [->|NZ]; [lia|].
          assert (INX : In (nx, 64) LBX).
          { eapply Permutation_in; [exact HP|]. right. apply in_or_app. left. exact (cj_chain_head_block _ _ _ _ _ CHN NZ). }
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INX) 4%nat; intros _ _ _ X4).
          try rewrite alloc_ceiling_eq in X4. lia. }
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. zstep. zstep.
        replace (ret_pc (wz AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta.
        eapply lscps_bind.
        { eapply (art_free_ok AI) with (lo := lo) (A := p) (n := 64) (tl := []); rewrite ?unsigned_lit by lia;
            first [ exact HL | eapply perm_in_head; exact HP | exact ST | exact ERR | exact MI | exact TP | reflexivity | exact BXge
                  | split; [lia| unfold PC0_FREE; lia]
                  | apply uwt_hook_nonfp; lia
                  | eapply (tinv_room TI); [exact TV| exact st_item]
                  | alia ]. }
        cbv beta. intros ms2 mo2 g2 PO.
        (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
        rewrite ?unsigned_lit in ST2, PR2, TP2 by lia.
        replace (ret_pc (Z_to_bv 64 0x82664)) with (Z_to_bv 64 0x82664) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HP (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP2.
        assert (CHN2 : cj_chain T m2 (S d0) nx Bn).
        { eapply cj_chain_pres; [exact CHN| exact PR2|]. intros b Hb. eapply Permutation_in; [exact HP2|]. apply in_or_app; left; exact Hb. }
        assert (LI2 : linv (cb_remove p LBX) TRS2 (BX - cost_free) m2 mo2 g2 fj).
        { split; [exact HL2|]. split; [exact ST2|]. split.
          { eapply cj_pres_rw_cells; [exact PR2| exact FR|]. left. cbn. lia. }
          split; [exact ERR2|]. split; [exact MI2|]. split.
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia| | intros f Hf; exact Hf].
            intros b Hb. eapply Permutation_in; [exact HP2|]. apply in_or_app; right; exact Hb. }
          split; [eapply gmono_trans; [exact GM| exact GM2]|].
          eapply (tinv_put TI); [exact TV| exact st_item| exact TP2]. }
        eapply (IHn (length Bn) ltac:(cbn in LEN; rewrite !length_app in LEN; lia) (S d0) nx Bn (cb_remove p LBX) TRS2 (BX - cost_free) m2 mo2 g2 fj);
          first [ exact Dle | exact LOd | exact CHN2 | exact HP2 | exact LI2
                | rewrite HBX, ?cost_free_eq; cbn [length]; rewrite ?Nat2Z.inj_succ; unfold cblock in *; lia
                | cbn in LEN |- *; rewrite ?length_app in LEN; lia ].
      Qed.
      (* [comment removed for export] *)
      Lemma tail2 : forall LBX TRSX BX m mo g fj (vs' : Z) rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x23 t3 t4 t5 t6,
        Permutation ((p, 64) :: Bk ++ Bn ++ LR) LBX -> linv LBX TRSX BX m mo g fj ->
        BX = BFINv + cost_free * Z.of_nat (length ((p, 64) :: Bk ++ Bn)) ->
        rw_cells bsegs m p (nodeB nx pv ch ty p1 vs' vi p2 vd ky) ->
        cj_str m ky Bk -> cj_chain T m (S d0) nx Bn ->
        LSCPS bsegs POST (LST 0x8270c rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + 24)) x19
                              (Z_to_bv 64 (Z.shiftr (p + 24) 3 + 2147450880)) x23 t3 t4 t5 t6 m) mo g.
      Proof.
        intros until t6. intros HP LI HBX ND SK CHN. (nelimp LI 8%nat; intros HL ST FR ERR MI PR GM TV).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold AMALLOC_STACK in LO1. pose proof SP1eq as E1. pose proof SPtop as SPT.
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
        try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
        pose proof (cj_str_range _ _ _ SK) as KR.
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros CR1 CR2 CR3).
        assert (NXS : nx <= bv_unsigned sp + -80).
        { destruct (Z.eq_dec nx 0) as [->|NZ]; [lia|].
          assert (INX : In (nx, 64) LBX).
          { eapply Permutation_in; [exact HP|]. right. apply in_or_app. right. apply in_or_app. left. exact (cj_chain_head_block _ _ _ _ _ CHN NZ). }
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INX) 4%nat; intros _ _ _ X4). try rewrite alloc_ceiling_eq in X4. lia. }
        (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros HK _ _ _). unfold AHOOKS in HK.
        lazymatch type of HK with cells_at _ ?mm ?a ?cs => change (ro_cells bsegs mm a cs) in HK end.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as SO.
        pose proof ND as ND'. unfold nodeB, wz, wb in ND. unfold AERRNO in ERR.
        eapply lscps_step_evt. cbv beta delta [mkR].
        (* [comment removed for export] *)
        pose proof (shadow_ok_shchk m p 64 (p + 24) 4 SO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. asan_chk CK4.
        zstep. zstep. zstep. if_lit.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shb0 m p 64 (p + 56) SO ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as Z56. asan_chk Z56. clear Z56.
        zstep. zstep. if_cases Kz; zify_cond Kz.
        - (* [comment removed for export] *)
          rewrite Kz in SK. pose proof (cj_str_zero_inv _ _ SK) as EBk. rewrite EBk in HP, HBX. cbn [app] in HP, HBX.
          apply evt_done. cbv beta. eapply tail3; [exact HP| exact LI| exact HBX| exact CHN].
        - (nelim (cj_str_nonzero_inv _ _ _ SK Kz) 7%nat; intros nk kstr ktail EBk _ _ _). rewrite EBk in HP, HBX. cbn [app] in HP. cbn [app length] in HBX.
          assert (BXge : cost_free <= BX) by (rewrite HBX; rewrite ?Nat2Z.inj_succ; rewrite cost_free_eq in *; lia).
          zstep. zstep.
          replace (ret_pc (wz AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply evt_done. cbv beta.
          assert (HP' : Permutation ((ky, nk) :: (p, 64) :: Bn ++ LR) LBX) by (eapply Permutation_trans; [apply perm_swap| exact HP]).
          eapply lscps_bind.
          { eapply (art_free_ok AI) with (lo := lo) (A := ky) (n := nk) (tl := []); rewrite ?unsigned_lit by lia;
              first [ exact HL | eapply perm_in_head; exact HP' | exact ST | exact ERR | exact MI | exact TP | reflexivity | exact BXge
                    | split; [lia| unfold PC0_FREE; lia]
                    | apply uwt_hook_nonfp; lia
                    | eapply (tinv_room TI); [exact TV| exact st_key]
                    | alia ]. }
          cbv beta. intros ms2 mo2 g2 PO.
          (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
          rewrite ?unsigned_lit in ST2, PR2, TP2 by lia.
          replace (ret_pc (Z_to_bv 64 0x82744)) with (Z_to_bv 64 0x82744) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          pose proof (perm_cb_remove _ _ _ _ HP' (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP2.
          apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists p, 64; split; [eapply perm_in_head; exact HP2| cbn; lia]].
          apply (cj_chain_pres _ _ _ _ _ _ _ _ _ _ CHN) in PR2 as CHN2.
          2:{ intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. left. exact Hb. }
          assert (PR3 : cj_pres sp0 LR LF (bv_unsigned sp) m0 m2).
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia| | intros f Hf; exact Hf].
            intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. right. exact Hb. }
          assert (TV2 : TINV TI np TRS2) by (eapply (tinv_put TI); [exact TV| exact st_key| exact TP2]).
          assert (GM3 : gmono g0 g2) by (eapply gmono_trans; [exact GM| exact GM2]).
          pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) as SO2.
          clear PR PR2 MI ST ERR HL CHN HK SO GM GM2 TV TP2.
          (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL2) 4%nat; intros HK _ _ _). unfold AHOOKS in HK.
          lazymatch type of HK with cells_at _ ?mm ?a ?cs => change (ro_cells bsegs mm a cs) in HK end.
          pose proof (conj ERR2 I) as ERRbox. clear ERR2.
          (* [comment removed for export] *)
          pose proof (munch_refl [(p + 56, p + 64)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
          eapply lscps_step_evt. cbv beta delta [mkR].
          pose proof (shadow_ok_shb0 m2 p 64 (p + 56) SO2 ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as Z56. asan_chk Z56. clear Z56.
          zstep. fix_lit_store. zstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
          assert (HL3 : ART AI sp0 SPB (cb_remove ky LBX) LF TRS2 (BX - cost_free) m3 mo2 g2).
          { eapply (art_block_store AI); [exact HL2| eapply perm_in_head; exact HP2| exact MU| exact WM| lia| lia]. }
          assert (PR4 : cj_pres sp0 LR LF (bv_unsigned sp) m0 m3).
          { eapply cj_pres_trans; [exact PR3|]. eapply (cj_pres_block_store AI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HP2); [| lia| exact SP0| exact MU| exact WM| lia| lia].
            intros b Hb. apply in_or_app. right. exact Hb. }
          assert (CHN3 : cj_chain T m3 (S d0) nx Bn).
          { eapply cj_chain_frame; [exact CHN2| exact MU| exact WM|].
            intros A' n' Hin. eapply (lheap_block_disjoint_from AI); [exact HL2| exact HP2| | | apply in_or_app; left; exact Hin]; lia. }
          assert (ERR3 : rw_cells bsegs m3 AERRNO [C4 errv]).
          { eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]. }
          apply evt_done. cbv beta.
          eapply tail3; [exact HP2| | | exact CHN3].
          + split; [exact HL3|]. split; [exact ST2|]. split; [exact FR|]. split; [exact ERR3|]. split; [assumption|]. split; [exact PR4|]. split; [exact GM3| exact TV2].
          + rewrite HBX. cbn [length]. rewrite ?Nat2Z.inj_succ. unfold cblock in *. rewrite ?cost_free_eq. lia.
      Qed.

      (* [comment removed for export] *)
      Lemma tail1 : forall LBX TRSX BX m mo g fj rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x23 t3 t4 t5 t6,
        Permutation ((p, 64) :: Bv ++ Bk ++ Bn ++ LR) LBX -> linv LBX TRSX BX m mo g fj ->
        BX = BFINv + cost_free * Z.of_nat (length ((p, 64) :: Bv ++ Bk ++ Bn)) ->
        rw_cells bsegs m p (nodeB nx pv ch ty p1 vs vi p2 vd ky) ->
        cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m (S d0) nx Bn ->
        LSCPS bsegs POST (LST 0x826c8 rav t0 t1 t2 (Z_to_bv 64 nx) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (p + 24)) x19
                              (Z_to_bv 64 (Z.shiftr (p + 24) 3 + 2147450880)) x23 t3 t4 t5 t6 m) mo g.
      Proof.
        intros until t6. intros HP LI HBX ND SV SK CHN. (nelimp LI 8%nat; intros HL ST FR ERR MI PR GM TV).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold AMALLOC_STACK in LO1. pose proof SP1eq as E1. pose proof SPtop as SPT.
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
        try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
        pose proof (cj_str_range _ _ _ SV) as VR.
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros CR1 CR2 CR3).
        assert (NXS : nx <= bv_unsigned sp + -80).
        { destruct (Z.eq_dec nx 0) as [->|NZ]; [lia|].
          assert (INX : In (nx, 64) LBX).
          { eapply Permutation_in; [exact HP|]. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact (cj_chain_head_block _ _ _ _ _ CHN NZ). }
          (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL INX) 4%nat; intros _ _ _ X4). try rewrite alloc_ceiling_eq in X4. lia. }
        (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros HK _ _ _). unfold AHOOKS in HK.
        lazymatch type of HK with cells_at _ ?mm ?a ?cs => change (ro_cells bsegs mm a cs) in HK end.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as SO.
        pose proof ND as ND'. unfold nodeB, wz, wb in ND. unfold AERRNO in ERR.
        eapply lscps_step_evt. cbv beta delta [mkR].
        (* [comment removed for export] *)
        pose proof (shadow_ok_shchk m p 64 (p + 24) 4 SO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. asan_chk CK4.
        zstep. zstep. zstep. if_lit.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shb0 m p 64 (p + 32) SO ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as Z32. asan_chk Z32. clear Z32.
        zstep. zstep. if_cases Kz; zify_cond Kz.
        - (* [comment removed for export] *)
          rewrite Kz in SV. pose proof (cj_str_zero_inv _ _ SV) as EBv. rewrite EBv in HP, HBX. cbn [app] in HP, HBX.
          apply evt_done. cbv beta. eapply tail2; [exact HP| exact LI| exact HBX| exact ND'| exact SK| exact CHN].
        - (nelim (cj_str_nonzero_inv _ _ _ SV Kz) 7%nat; intros nv vstr vtail EBv _ _ _). rewrite EBv in HP, HBX. cbn [app] in HP. cbn [app length] in HBX.
          assert (BXge : cost_free <= BX) by (rewrite HBX; rewrite ?Nat2Z.inj_succ; rewrite cost_free_eq in *; lia).
          zstep. zstep.
          replace (ret_pc (wz AFREE)) with (wz AFREE) by (unfold wz, AFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply evt_done. cbv beta.
          assert (HP' : Permutation ((vs, nv) :: (p, 64) :: Bk ++ Bn ++ LR) LBX) by (eapply Permutation_trans; [apply perm_swap| exact HP]).
          eapply lscps_bind.
          { eapply (art_free_ok AI) with (lo := lo) (A := vs) (n := nv) (tl := []); rewrite ?unsigned_lit by lia;
              first [ exact HL | eapply perm_in_head; exact HP' | exact ST | exact ERR | exact MI | exact TP | reflexivity | exact BXge
                    | split; [lia| unfold PC0_FREE; lia]
                    | apply uwt_hook_nonfp; lia
                    | eapply (tinv_room TI); [exact TV| exact st_vs]
                    | alia ]. }
          cbv beta. intros ms2 mo2 g2 PO.
          (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
          rewrite ?unsigned_lit in ST2, PR2, TP2 by lia.
          replace (ret_pc (Z_to_bv 64 0x82700)) with (Z_to_bv 64 0x82700) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          pose proof (perm_cb_remove _ _ _ _ HP' (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP2.
          apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists p, 64; split; [eapply perm_in_head; exact HP2| cbn; lia]].
          apply (cj_chain_pres _ _ _ _ _ _ _ _ _ _ CHN) in PR2 as CHN2.
          2:{ intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
          apply (cj_str_pres _ _ _ _ _ _ _ _ SK) in PR2 as SK2.
          2:{ intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. left. exact Hb. }
          assert (PR3 : cj_pres sp0 LR LF (bv_unsigned sp) m0 m2).
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia| | intros f Hf; exact Hf].
            intros b Hb. eapply Permutation_in; [exact HP2|]. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
          assert (TV2 : TINV TI np TRS2) by (eapply (tinv_put TI); [exact TV| exact st_vs| exact TP2]).
          assert (GM3 : gmono g0 g2) by (eapply gmono_trans; [exact GM| exact GM2]).
          pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HP2)) as SO2.
          clear PR PR2 MI ST ERR HL CHN HK SO GM GM2 TV TP2 SK SV.
          (nelimp (art_cjst AI _ _ _ _ _ _ _ _ _ HL2) 4%nat; intros HK _ _ _). unfold AHOOKS in HK.
          lazymatch type of HK with cells_at _ ?mm ?a ?cs => change (ro_cells bsegs mm a cs) in HK end.
          pose proof (conj ERR2 I) as ERRbox. clear ERR2.
          (* [comment removed for export] *)
          pose proof (munch_refl [(p + 32, p + 40)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
          eapply lscps_step_evt. cbv beta delta [mkR].
          pose proof (shadow_ok_shb0 m2 p 64 (p + 32) SO2 ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as Z32. asan_chk Z32. clear Z32.
          zstep. fix_lit_store.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
          assert (HL3 : ART AI sp0 SPB (cb_remove vs LBX) LF TRS2 (BX - cost_free) m3 mo2 g2).
          { eapply (art_block_store AI); [exact HL2| eapply perm_in_head; exact HP2| exact MU| exact WM| lia| lia]. }
          assert (PR4 : cj_pres sp0 LR LF (bv_unsigned sp) m0 m3).
          { eapply cj_pres_trans; [exact PR3|]. eapply (cj_pres_block_store AI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HP2); [| lia| exact SP0| exact MU| exact WM| lia| lia].
            intros b Hb. apply in_or_app. right. apply in_or_app. right. exact Hb. }
          assert (CHN3 : cj_chain T m3 (S d0) nx Bn).
          { eapply cj_chain_frame; [exact CHN2| exact MU| exact WM|].
            intros A' n' Hin. eapply (lheap_block_disjoint_from AI); [exact HL2| exact HP2| | | apply in_or_app; right; apply in_or_app; left; exact Hin]; lia. }
          assert (SK3 : cj_str m3 ky Bk).
          { eapply cj_str_frame; [exact SK2| exact MU| exact WM|].
            intros A' n' Hin. eapply (lheap_block_disjoint_from AI); [exact HL2| exact HP2| | | apply in_or_app; left; exact Hin]; lia. }
          assert (ERR3 : rw_cells bsegs m3 AERRNO [C4 errv]).
          { eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]. }
          apply evt_done. cbv beta.
          eapply (tail2 (cb_remove vs LBX) TRS2 (BX - cost_free) m3 mo2 g2 fj 0); [exact HP2| | | | exact SK3| exact CHN3].
          + split; [exact HL3|]. split; [exact ST2|]. split; [exact FR|]. split; [exact ERR3|]. split; [assumption|]. split; [exact PR4|]. split; [exact GM3| exact TV2].
          + rewrite HBX. cbn [length app]. rewrite ?length_app. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add. unfold cblock in *. rewrite ?cost_free_eq. lia.
          + unfold nodeB, wz, wb. exact ND.
      Qed.

      (* [comment removed for export] *)
      Lemma node_body : forall LBX TRSX BX m mo g fj rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6,
        Permutation (((p, 64) :: Bv ++ Bk ++ Bc ++ Bn) ++ LR) LBX -> linv LBX TRSX BX m mo g fj ->
        BX = BFINv + cost_free * Z.of_nat (length ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn)) ->
        rw_cells bsegs m p (nodeB nx pv ch ty p1 vs vi p2 vd ky) ->
        cj_str m vs Bv -> cj_str m ky Bk -> cj_chain T m d0 ch Bc -> cj_chain T m (S d0) nx Bn ->
        LSCPS bsegs POST (LST 0x82668 rav t0 t1 t2 (Z_to_bv 64 p) s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 m) mo g.
      Proof.
        intros until t6. intros HP LI HBX ND SV SK CHC CHN. (nelimp LI 8%nat; intros HL ST FR ERR MI PR GM TV).
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold AMALLOC_STACK in LO1. pose proof SP1eq as E1. pose proof SPtop as SPT.
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
        try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHC) 3%nat; intros CR1 CR2 CR3).
        (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros NR1 NR2 NR3).
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as SO.
        pose proof ND as ND'. unfold nodeB, wz, wb in ND. unfold AERRNO in ERR.
        eapply lscps_step_evt. cbv beta delta [mkR].
        (* [comment removed for export] *)
        zstep. replace (Z.land p 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
        zstep. if_cases G; zify_cond G; [exfalso; lia|]. clear G.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shb0 m p 64 p SO ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as Z0.
        replace p with (p + 0) in Z0 at 2 by lia. asan_chk Z0. clear Z0.
        zstep. zstep. zstep.
        pose proof (shadow_ok_shchk m p 64 (p + 24) 4 SO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as CK4. asan_chk CK4.
        (* [comment removed for export] *)
        zstep. zstep. zstep. if_lit.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shb0 m p 64 (p + 16) SO ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as Z16. asan_chk Z16. clear Z16.
        zstep. zstep. if_cases Kc; zify_cond Kc.
        - (* [comment removed for export] *)
          rewrite Kc in CHC. pose proof (cj_chain_null_inv _ _ _ _ CHC) as EBc. rewrite EBc in HP, HBX.
          apply evt_done. cbv beta. eapply tail1; [| exact LI| | exact ND'| exact SV| exact SK| exact CHN].
          + eapply Permutation_trans; [apply perm_node_nokids| exact HP].
          + rewrite HBX. cbn [app length]. rewrite ?length_app. cbn [length]. unfold cblock in *. lia.
        - (* [comment removed for export] *)
          zstep. change (Z_to_bv 64 534036) with (wz DELETE_ENTRY). apply evt_done. cbv beta.
          assert (HPk : Permutation (Bc ++ (p, 64) :: Bv ++ Bk ++ Bn ++ LR) LBX) by (eapply Permutation_trans; [apply perm_node_kids| exact HP]).
          eapply lscps_bind.
          { pose proof (REC d0 ltac:(lia)) as DS. unfold delete_spec_at in DS.
            eapply DS with (lo := lo) (LR := (p, 64) :: Bv ++ Bk ++ Bn ++ LR) (B := Bc); clear DS; rewrite ?unsigned_lit by lia;
              first [ exact HL | exact CHC | exact HPk | exact ST | exact ERR | exact MI | exact TP | exact TV | exact SDEL | exact SP0 | reflexivity | alia
                    | rewrite HBX; rewrite ?cost_free_eq in *; cbn [length app]; rewrite ?length_app; rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add; unfold cblock in *; lia
                    | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity ]. }
          cbv beta. intros ms2 mo2 g2 PO.
          (nelim PO 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 TRS2 -> MI2 ST2 ERR2 HL2 HP2 TV2 GM2 PR2)
.
          rewrite ?unsigned_lit in ST2, PR2 by lia.
          replace (ret_pc (Z_to_bv 64 0x826c8)) with (Z_to_bv 64 0x826c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          apply Permutation_sym in HP2.
          apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in FR; [| left; cbn; lia].
          apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ PR2) in ND; [| do 3 right; left; exists p, 64; split; [left; reflexivity| cbn; lia]].
          apply (cj_chain_pres _ _ _ _ _ _ _ _ _ _ CHN) in PR2 as CHN2.
          2:{ intros b Hb. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hb. }
          apply (cj_str_pres _ _ _ _ _ _ _ _ SV) in PR2 as SV2. 2:{ intros b Hb. right. apply in_or_app; left. exact Hb. }
          apply (cj_str_pres _ _ _ _ _ _ _ _ SK) in PR2 as SK2. 2:{ intros b Hb. right. apply in_or_app; right. apply in_or_app; left. exact Hb. }
          assert (PR3 : cj_pres sp0 LR LF (bv_unsigned sp) m0 m2).
          { eapply cj_pres_trans; [exact PR|]. eapply cj_pres_weaken; [exact PR2| lia| | intros f Hf; exact Hf].
            intros b Hb. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb. }
          assert (GM3 : gmono g0 g2) by (eapply gmono_trans; [exact GM| exact GM2]).
          eapply (tail1 LR2 TRS2 (BX - cost_free * Z.of_nat (length Bc)) m2 mo2 g2 fj); [exact HP2| | | | exact SV2| exact SK2| exact CHN2].
          + split; [| split; [exact ST2|]]; [| split; [exact FR|]; split; [exact ERR2|]; split; [exact MI2|]; split; [exact PR3|]; split; [exact GM3| exact TV2]].
            eapply (art_perm AI); [exact HL2| apply Permutation_refl| apply Permutation_refl].
          + rewrite HBX, ?cost_free_eq. cbn [length app]. rewrite ?length_app. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add. unfold cblock in *. lia.
          + unfold nodeB, wz, wb. exact ND.
      Qed.
    End Body.

    (* [comment removed for export] *)
    Lemma test_spec : forall n, TestSpec n.
    Proof.
      induction n as [n IHn] using lt_wf_ind. unfold TestSpec.
      intros d p B LBX TRSX BX m mo g fj rav t0 t1 t2 s1v a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x22 x23 t3 t4 t5 t6 LEN Dle LOd HBX CH HP LI.
      destruct (Z.eq_dec p 0) as [->|PNZ].
      - pose proof (cj_chain_null_inv _ _ _ _ CH) as ->. cbn [app] in HP. cbn [length] in HBX.
        replace BX with BFINv in LI by lia. eapply loop_exit; [exact HP| exact LI].
      - (nelim (cj_chain_cons_inv _ _ _ _ _ CH PNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn -> ND TY _ SV SK CHC CHN ->)
.
        (nelimp LI 6%nat; intros HL _ _ _ MI _).
        (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 _ _ R4).
        try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
        pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO1 as LO1'. unfold AMALLOC_STACK in LO1'.
        eapply lscps_step_evt. cbv beta delta [mkR].
        zstep. if_cases K; zify_cond K; [exfalso; exact (PNZ K)|]. clear K.
        apply evt_done. cbv beta.
        eapply (node_body n IHn d0 p nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn Dle LOd LEN PNZ);
          [exact HP| exact LI| exact HBX| apply nodeB_of_node; [exact TY| exact ND]| exact SV| exact SK| exact CHC| exact CHN].
    Qed.

    (* [comment removed for export] *)
    Lemma entry_body : forall (d0 : nat) (p : Z) (B LB : list cblock) (TRS : list (list Z)) (mo : Model)
        (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      (S d0 <= dk)%nat -> lo <= bv_unsigned sp - DELETE_STACK (S d0) ->
      ART AI sp0 SPB LB LF TRS B0 m0 mo g0 -> cj_chain T m0 (S d0) p B -> p <> 0 -> Permutation (B ++ LR) LB -> NB = length B ->
      stk bsegs m0 lo (bv_unsigned sp) -> rw_cells bsegs m0 AERRNO [C4 errv] -> mem_inv bsegs m0 -> TINV TI np TRS ->
      LSCPS bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz DELETE_ENTRY) fc None m0 (seg_rom bsegs)) mo g0.
    Proof.
      intros until t6. intros Dle LOd HL CH PNZ HP HNB ST ERR MI TV.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO1 as LO1'. unfold AMALLOC_STACK in LO1'. pose proof SPtop as SPT.
      (nelim (cj_chain_cons_inv _ _ _ _ _ CH PNZ) 24%nat; intros d0' nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn Ed ND TY _ SV SK CHC CHN ->)
.
      injection Ed as <-.
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4).
      try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
      pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB. shbase_split SB.
      unfold AERRNO in ERR. pose proof (conj ERR I) as ERRbox. clear ERR. pose proof (conj ND I) as NDbox. clear ND.
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
      unfold DELETE_ENTRY, wz. eapply lscps_step_evt. cbv beta delta [mkR].
      carve_frame 80%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      do 10 zstep.
      zstep. if_cases K; zify_cond K; [exfalso; exact (PNZ K)|]. clear K.
      do 6 zstep.
      apply evt_done. cbv beta.
      lazymatch goal with |- LSCPS _ _ (MS _ _ _ _ _ ?mc _) _ _ => rename mc into m1 end.
      assert (HL1 : ART AI sp0 SPB LB LF TRS B0 m1 mo g0).
      { eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]. }
      assert (PR1 : cj_pres sp0 LB LF (bv_unsigned sp) m0 m1).
      { eapply (cj_pres_stack_store AI); [exact HL| intros b Hb; exact Hb| exact MU| exact WM| alia| lia]. }
      assert (ERR1 : rw_cells bsegs m1 AERRNO [C4 errv]).
      { eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]. }
      assert (INB : forall b, In b ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn) -> In b LB).
      { intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. }
      lazymatch goal with FRc : rw_cells bsegs m1 (bv_unsigned sp + -80) (?c0 :: _), STc : stk bsegs m1 lo _ |- _ =>
        lazymatch c0 with CB 8 ?fj =>
        eapply (node_body (length ((p, 64) :: Bv ++ Bk ++ Bc ++ Bn)) (fun n' _ => test_spec n') d0 p nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bc Bn
                  Dle LOd (Nat.le_refl _) PNZ LB TRS B0 m1 mo g0 fj);
          [ exact HP | | | apply nodeB_of_node; [exact TY|] | | | | ] end end.
      - split; [exact HL1|]. split; [assumption|]. split; [assumption|]. split; [exact ERR1|]. split; [assumption|].
        split; [| split; [apply gmono_refl| exact TV]].
        eapply cj_pres_weaken; [exact PR1| lia| | intros f Hf; exact Hf]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact Hb.
      - rewrite HNB. cbn [length app]. rewrite ?length_app. unfold cblock in *. rewrite ?cost_free_eq. lia.
      - eapply cj_pres_rw_cells; [exact PR1| exact (proj1 NDbox)|]. do 3 right. left. exists p, 64. split; [apply INB; left; reflexivity| rewrite node_cells_size; lia].
      - eapply cj_str_pres; [exact SV| exact PR1|]. intros b Hb. apply INB. right. apply in_or_app. left. exact Hb.
      - eapply cj_str_pres; [exact SK| exact PR1|]. intros b Hb. apply INB. right. apply in_or_app; right. apply in_or_app; left. exact Hb.
      - eapply cj_chain_pres; [exact CHC| exact PR1|]. intros b Hb. apply INB. right. do 2 (apply in_or_app; right). apply in_or_app; left. exact Hb.
      - eapply cj_chain_pres; [exact CHN| exact PR1|]. intros b Hb. apply INB. right. do 3 (apply in_or_app; right). exact Hb.
    Qed.
  End Loop.

  (* [comment removed for export] *)
  Lemma delete_spec_upto : forall dk, (forall d, (d < dk)%nat -> delete_spec_at AI TI d) ->
    forall d, (d <= dk)%nat -> delete_spec_at AI TI d.
  Proof.
    intros dk REC d Hd. unfold delete_spec_at. intros until errv. intros HL CH HP SPBle SP0 TOP SPAL ST CEIL BOT LO ERR MI TP A0 TV SDEL COST.
    subst a0. pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'.
    pose proof ST as STc; (nelim STc 3%nat; intros _ SPhi _).
    assert (LO0 : lo <= bv_unsigned sp - AMALLOC_STACK) by (unfold DELETE_STACK in LO; lia). unfold AMALLOC_STACK in LO0.
    assert (SPT : bv_unsigned sp + 16 <= sp0 + 4096) by (clear -TOP; unfold ASTACK_TOP, roundup in TOP; Z.div_mod_to_equations; lia).
    destruct (Z.eq_dec p 0) as [->|PNZ].
    - (* [comment removed for export] *)
      pose proof (cj_chain_null_inv _ _ _ _ CH) as ->. cbn [app] in HP. cbn [length] in COST |- *.
      unfold AERRNO in ERR. pose proof (conj ERR I) as ERRbox. clear ERR.
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
      unfold DELETE_ENTRY, wz. eapply lscps_step_evt. cbv beta delta [mkR].
      carve_frame 80%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      do 10 zstep.
      zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      do 11 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      lazymatch goal with FRc : rw_cells bsegs m1 (bv_unsigned sp + -80) _, STc : stk bsegs m1 lo _ |- _ => release_frame FRc STc (bv_unsigned sp) end.
      apply evt_done. apply lscps_done. unfold delete_post.
      nexists 18%nat. split; [reflexivity|].
      split; [assumption|]. split; [assumption|].
      split; [eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]|].
      split. { rewrite Z.mul_0_r, Z.sub_0_r. eapply (art_perm AI); [eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]| apply Permutation_sym; exact HP| apply Permutation_refl]. }
      split; [apply Permutation_refl|]. split; [exact TV|]. split; [apply gmono_refl|].
      assert (PR1 : cj_pres sp0 LB LF (bv_unsigned sp) m m1).
      { eapply (cj_pres_stack_store AI); [exact HL| intros b Hb; exact Hb| exact MU| exact WM| alia| lia]. }
      eapply cj_pres_weaken; [exact PR1| lia| | intros f Hf; exact Hf].
      intros b Hb. eapply Permutation_in; [exact HP| exact Hb].
    - destruct d as [|d0]; [exfalso; destruct (cj_chain_zero_budget _ _ _ _ CH) as [E _]; exact (PNZ E)|].
      eapply (entry_body dk REC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m g sp0 SPB LR LF np B0 (length B) lo errv T
                TP SPBle SP0 TOP SPAL CEIL BOT ltac:(unfold DELETE_STACK in LO |- *; lia) SPhi SDEL);
        first [ exact Hd | exact LO | exact HL | exact CH | exact PNZ | exact HP | reflexivity | exact ST | exact ERR | exact MI | exact TV
              | unfold cblock in *; rewrite ?cost_free_eq in *; lia ].
  Qed.

  Theorem cjson_delete_spec : cjson_delete_stmt AI TI.
  Proof.
    intros d. induction d as [d IH] using lt_wf_ind.
    apply (delete_spec_upto d); [| apply Nat.le_refl]. intros d' Hd'. apply IH. exact Hd'.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac alia := unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; rewrite ?alloc_ceiling_eq; unfold DELETE_STACK, AMALLOC_STACK in *; lia.
End CJ_delete.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
Module CJ_minify.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition MINIFY_ENTRY : Z := 0x84fcc.
Definition MINIFY_STACK : Z := 48.
Definition MJT : Z := 0x20f4c.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition JT : list byte := map wb
  [200; 67; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0;
   36; 66; 6; 0; 228; 64; 6; 0; 228; 64; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 228; 64; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0;
   36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0;
   36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0;
   228; 64; 6; 0; 36; 66; 6; 0; 28; 65; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0;
   36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 36; 66; 6; 0; 76; 66; 6; 0].

Definition jt_sel (c : Z) : Z :=
  if c =? 0 then 0x643c8
  else if (c =? 9) || (c =? 10) || (c =? 13) || (c =? 32) then 0x640e4
  else if c =? 34 then 0x6411c else if c =? 47 then 0x6424c else 0x64224.

Lemma jt_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m MJT JT.
Proof.
  intros m MI.
  pose proof (ro_cells_image bsegs m MJT JT MI ltac:(vm_compute; reflexivity) ltac:(unfold MJT; lia) ltac:(unfold MJT; cbn; lia)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  inversion H. f_equal; [apply bv_eq; assumption| apply IH; assumption].
Qed.

Lemma jt_entry : forall c, 0 <= c <= 47 ->
  firstn 4 (skipn (Z.to_nat (Z.shiftl c 2)) JT) = le4 (Z_to_bv 64 (jt_sel c)).
Proof.
  intros c Hc.
  assert (H : exists n, c = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat c); lia).
  (nelim H 3%nat; intros n -> Hn).
  do 48 (destruct n as [|n]; [apply byte_list_eq; vm_compute; reflexivity|]). lia.
Qed.

Lemma jt_read : forall m c, mem_inv bsegs m -> 0 <= c <= 47 ->
  ov_read_bytes bsegs m (wa (Z.shiftl c 2 + MJT)) 4 = Some (le4 (Z_to_bv 64 (jt_sel c))).
Proof.
  intros m c MI Hc. rewrite Z.add_comm, <- jt_entry by exact Hc.
  apply (bytes_at_read bsegs m MJT JT (Z.shiftl c 2) 4 (jt_bytes m MI)).
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
  - change (length JT) with 192%nat. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma jt_sel_default : forall c, c <> 0 -> c <> 9 -> c <> 10 -> c <> 13 -> c <> 32 -> c <> 34 -> c <> 47 ->
  jt_sel c = 0x64224.
Proof.
  intros. unfold jt_sel.
  repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y); [lia|] end. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sufx (orig buf : list byte) (q : Z) : Prop :=
  length buf = length orig /\ forall x, 0 <= x -> q <= x -> nth_error buf (Z.to_nat x) = nth_error orig (Z.to_nat x).

Lemma sufx_refl : forall orig q, sufx orig orig q.
Proof. intros. split; [reflexivity| intros; reflexivity]. Qed.

Lemma sufx_mono : forall orig buf q q', sufx orig buf q -> q <= q' -> sufx orig buf q'.
Proof. intros orig buf q q' [L H] Hq. split; [exact L|]. intros x H0 Hx. apply H; lia. Qed.

Lemma sufx_upd : forall orig buf q k b,
  sufx orig buf q -> 0 <= k -> (k < q \/ nth_error orig (Z.to_nat k) = Some b) ->
  sufx orig (upd buf (Z.to_nat k) b) q.
Proof.
  intros orig buf q k b [L H] Hk Hb. split; [rewrite upd_length; exact L|].
  intros x H0 Hx. destruct (Z.eq_dec k x) as [<-|NE].
  - destruct Hb as [Hb|Hb]; [lia|]. rewrite Hb.
    destruct (Nat.lt_ge_cases (Z.to_nat k) (length buf)) as [LT|GE].
    + apply nth_error_upd_same. exact LT.
    + exfalso. assert (E : nth_error orig (Z.to_nat k) = None) by (apply nth_error_None; lia). rewrite E in Hb. discriminate.
  - rewrite nth_error_upd_other by lia. apply H; lia.
Qed.

Lemma sufx_nth : forall orig buf q x b,
  sufx orig buf q -> q <= x -> 0 <= x -> nth_error orig (Z.to_nat x) = Some b -> nth_error buf (Z.to_nat x) = Some b.
Proof. intros orig buf q x b [L H] Hx H0 Hb. rewrite H by lia. exact Hb. Qed.

Lemma mf_store : forall m A buf (k : Z) (b : byte),
  u8arr bsegs m A buf -> 0 <= k < Z.of_nat (length buf) ->
  store_ok bsegs m (wa (A + k)) 1 = true /\ u8arr bsegs (write_to_mem m (wa (A + k)) [b]) A (upd buf (Z.to_nat k) b).
Proof.
  intros m A buf k b ARR Hk. split.
  - eapply u8arr_store_ok; [exact ARR| exact Hk| reflexivity].
  - apply u8arr_write; [exact ARR| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition minify_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (n : nat) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(A, A + Z.of_nat n); (lo, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ (exists buf', u8arr bsegs m' A buf' /\ length buf' = n /\ In (wb 0) buf').

Section Proofs.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (A lo : Z) (s : list byte).
  Hypothesis NONUL : ~ In (wb 0) s.
  Hypothesis AB : AIMG_HI <= A /\ A + Z.of_nat (length s) + 1 <= alloc_ceiling.
  Hypothesis LOB : alloc_ceiling <= lo /\ lo + 48 <= bv_unsigned sp.
  Hypothesis TS0 : text_sh m0 A (Z.of_nat (length s) + 1).
  (* [comment removed for export] *)
  Hypothesis ABND : sclr A (Z.of_nat (length s) + 1).

  Notation len := (Z.of_nat (length s)).
  Notation orig := (s ++ [wb 0]).
  Notation SP := (bv_unsigned sp).
  Notation W := [(A, A + Z.of_nat (S (length s))); (lo, SP)].
  Notation POST := (minify_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (S (length s)) lo m0).
  Notation M1 := 18446744073709551615 (only parsing).
  Notation M3 := 18446744073709551613 (only parsing).
  (* [comment removed for export] *)
  Notation ST pc mm x8 x9 x10 x11 x12 x13 x18 x19 x20 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp (Z_to_bv 64 2147450880) (Z_to_bv 64 92) (Z_to_bv 64 MJT) x8 x9 x10 x11 x12 x13
             (Z_to_bv 64 47) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 34) x18 x19 x20 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 M1) (Z_to_bv 64 42) (Z_to_bv 64 M3) (Z_to_bv 64 10))
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Definition FRAME : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Definition inv (buf : list byte) (m : word -> option byte) (q : Z) : Prop :=
    u8arr bsegs m A buf /\ sufx orig buf q /\ munch W m0 m /\ wmono bsegs m0 m /\ mem_inv bsegs m
    /\ stk bsegs m lo (SP + -48) /\ rw_cells bsegs m (SP + -48) FRAME.

  Lemma orig_length : length orig = S (length s).
  Proof. rewrite length_app. cbn. lia. Qed.

  Lemma orig_nth_lt : forall x, 0 <= x < len -> exists b, nth_error orig (Z.to_nat x) = Some b /\ bv_unsigned b <> 0.
  Proof.
    intros x Hx. destruct (nth_error s (Z.to_nat x)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      intros Hb. apply NONUL. replace (wb 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  Lemma orig_nth_len : nth_error orig (Z.to_nat len) = Some (wb 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  Lemma orig_nth : forall x, 0 <= x <= len -> exists b, nth_error orig (Z.to_nat x) = Some b /\ (bv_unsigned b = 0 <-> x = len).
  Proof.
    intros x Hx. destruct (Z.eq_dec x len) as [->|NE].
    - exists (wb 0). split; [apply orig_nth_len|]. split; [auto| reflexivity].
    - (nelim (orig_nth_lt x ltac:(lia)) 3%nat; intros b Hb NZ). exists b. split; [exact Hb|]. split; [intros H; exfalso; exact (NZ H)| intros; lia].
  Qed.

  Lemma orig_nth_nz : forall x b, nth_error orig (Z.to_nat x) = Some b -> bv_unsigned b <> 0 -> 0 <= x -> x < len.
  Proof.
    intros x b Hb NZ Hx. destruct (Z.lt_ge_cases x len) as [LT|GE]; [exact LT|]. exfalso.
    destruct (Z.eq_dec x len) as [->|NE].
    - rewrite orig_nth_len in Hb. inversion Hb; subst. apply NZ. reflexivity.
    - assert (E : nth_error orig (Z.to_nat x) = None) by (apply nth_error_None; rewrite orig_length; lia). rewrite E in Hb. discriminate.
  Qed.

  Lemma orig_nth_val : forall x b v, nth_error orig (Z.to_nat x) = Some b -> bv_unsigned b = v -> b = wb v.
  Proof. intros x b v _ E. apply bv_eq. rewrite <- E. unfold wb. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

  Lemma inv_read : forall buf m q x, inv buf m q -> q <= x -> 0 <= x <= len ->
    exists b, nth_error orig (Z.to_nat x) = Some b /\ (bv_unsigned b = 0 <-> x = len)
      /\ ov_read_bytes bsegs m (wa (A + x)) 1 = Some [b] /\ 0 <= bv_unsigned b < 256.
  Proof.
    intros buf m q x (ARR & SX & _) Hq Hx. (nelim (orig_nth x Hx) 3%nat; intros b Hb Hz).
    exists b. split; [exact Hb|]. split; [exact Hz|]. split.
    - eapply u8arr_read; [exact ARR| eapply sufx_nth; [exact SX| exact Hq| lia| exact Hb]| lia| reflexivity].
    - pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
  Qed.

  Lemma inv_chk : forall buf m q x, inv buf m q -> 0 <= x <= len -> shchk m (A + x) 1.
  Proof.
    intros buf m q x (_ & _ & MU & _) Hx. pose proof AB as [A1 A2]. pose proof ABND as ABND'. sclr_lits ABND'. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1. bandM. sepM. try rewrite alloc_ceiling_eq in A2.
    pose proof LOB as [L1 L2]. try rewrite alloc_ceiling_eq in L1.
    (nelim (TS0 (A + x) ltac:(lia)) 3%nat; intros v Hv Cv). exists v. split; [|exact Cv].
    pose proof (SH_bounds (A + x) ltac:(lia)).
    eapply shb_munch; [exact Hv| exact MU| lia|]. cbn. unfold SH, SHADOW_OFFSET in *. Z.div_mod_to_equations. lia.
  Qed.

  Ltac lits := pose proof ABND as ABND'; sclr_lits ABND'; pose proof AB as [A1 A2]; unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in A1; try rewrite alloc_ceiling_eq in A2;
               pose proof LOB as [L1 L2]; try rewrite alloc_ceiling_eq in L1;
               pose proof (bv_unsigned_in_range 64 sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.

  Ltac do_store k b tac :=
    lazymatch goal with
    | ARR : u8arr bsegs ?m A ?buf |- _ =>
        let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
        destruct (mf_store m A buf k b ARR) as [SOK ARR'];
        [ lia
        | clear ARR; step;
          lazymatch goal with
          | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
              replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa (A + k)) [b])
                by (f_equal; first [tac| unfold wa; f_equal; lia]);
              store_done; rename ARR' into ARR
          end ]
    end.

  Ltac rd INV x b :=
    let Hn := fresh "Hn" b in let Hz := fresh "Hz" b in let RD := fresh "RD" in let R := fresh "R" b in
    destruct (inv_read _ _ _ x INV) as (b & Hn & Hz & RD & R); [lia| lia|]. (* [comment removed for export] *)

  Ltac chk INV x :=
    let CK := fresh "CK" in
    pose proof (inv_chk _ _ _ x INV ltac:(lia)) as CK; asan_chk CK.

  Ltac inv_parts INV :=
    lazymatch type of INV with inv _ _ _ =>
      let ARR := fresh "ARR" in let SX := fresh "SX" in let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in
      let STK := fresh "STK" in let FR := fresh "FR" in let Lbuf := fresh "Lbuf" in
      pose proof INV as (ARR & SX & MU & WM & MI & STK & FR); (* [comment removed for export] *)
      pose proof (proj1 SX) as Lbuf; rewrite orig_length in Lbuf
    end.

  Ltac mk_inv name q :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with ARR : u8arr bsegs mc A ?buf |- _ =>
        assert (name : inv buf mc q);
        [ split; [exact ARR| split; [| split; [assumption| split; [assumption| split; [assumption| split; [assumption| assumption]]]]]] |]
      end end.

  (* [comment removed for export] *)
  Ltac guard1 := let G := fresh "G" in zstep; if_cases G; zify_cond G; [exfalso; lia|].
  Ltac guard2 := let G := fresh "G" in zstep; if_cases G; zify_cond G; [| exfalso; lia].

  Section Head.
    Variable K : nat.
    Hypothesis IH : forall (j i : Z) (buf : list byte) (m : word -> option byte) (x8 x9 x12 x13 x18 x19 x20 : word),
      (Z.to_nat (len - j) < K)%nat -> 0 <= i <= j -> j <= len -> inv buf m j ->
      evt bsegs POST (ST 0x85038 m x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x12 x13 x18 x19 x20).

    (* [comment removed for export] *)
    Lemma l_default : forall j i buf m b x8 x9 x11 x18 x19 x20,
      (Z.to_nat (len - (j + 1)) < K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      nth_error orig (Z.to_nat j) = Some b ->
      evt bsegs POST (ST 0x85170 m x8 x9 (Z_to_bv 64 (A + i)) x11 (Z_to_bv 64 (A + j)) (Z_to_bv 64 (bv_unsigned b)) x18 x19 x20).
    Proof.
      intros j i buf m b x8 x9 x11 x18 x19 x20 HK Hij Hj INV Hb. inv_parts INV. lits. bandM. sepM.
      zstep. zstep. chk INV i.
      zstep.                                                  (* [comment removed for export] *)
      do_store i b ltac:(symmetry; apply le1_zxb).
      mk_inv INV1 (j + 1). { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia| left; lia]. }
      guard1.                                                 (* [comment removed for export] *)
      zstep.                                                  (* [comment removed for export] *)
      replace (A + j + 1) with (A + (j + 1)) by lia. replace (A + i + 1) with (A + (i + 1)) by lia.
      guard2.                                                 (* [comment removed for export] *)
      eapply (IH (j + 1) (i + 1)); [exact HK| lia| lia| exact INV1].
    Qed.

    (* [comment removed for export] *)
    Lemma l_ws : forall j i buf m x8 x9 x11 x13 x18 x19 x20,
      (Z.to_nat (len - (j + 1)) < K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      evt bsegs POST (ST 0x85030 m x8 x9 (Z_to_bv 64 (A + i)) x11 (Z_to_bv 64 (A + j)) x13 x18 x19 x20).
    Proof.
      intros j i buf m x8 x9 x11 x13 x18 x19 x20 HK Hij Hj INV. inv_parts INV. lits. bandM. sepM.
      zstep. replace (A + j + 1) with (A + (j + 1)) by lia.
      guard1.                                                 (* [comment removed for export] *)
      apply (IH (j + 1) i buf m); [exact HK| lia| lia|].
      destruct INV as (ARR' & _ & R'). split; [exact ARR'|]. split; [eapply sufx_mono; [exact SX| lia]| exact R']. (* [comment removed for export] *)
    Qed.

    (* [comment removed for export] *)
    Lemma l_nul : forall j i buf m x8 x9 x11 x12 x13 x18 x19 x20,
      0 <= i <= j -> j <= len -> inv buf m j ->
      evt bsegs POST (ST 0x85314 m x8 x9 (Z_to_bv 64 (A + i)) x11 x12 x13 x18 x19 x20).
    Proof.
      intros j i buf m x8 x9 x11 x12 x13 x18 x19 x20 Hij Hj INV. inv_parts INV. lits. bandM. sepM. unfold FRAME in FR.
      zstep. zstep. chk INV i.
      do_store i (wb 0) ltac:(apply byte_list_eq; reflexivity).
      do 6 zstep.
      lazymatch goal with ST' : stk bsegs ?mc lo _, FR' : rw_cells bsegs ?mc (bv_unsigned sp + -48) _ |- _ => release_frame FR' ST' (bv_unsigned sp) end.
      zstep. zstep. apply evt_done. unfold minify_post. do 15 eexists. eexists. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      eexists. split; [exact ARR|]. split; [rewrite upd_length; exact Lbuf|].
      eapply nth_error_In. apply nth_error_upd_same. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma sl_loop : forall (kk : nat) p o buf m x8 x9 x11 x13 x18 x19 x20,
      (Z.to_nat (len - (p + 1)) <= kk)%nat -> (Z.to_nat (len - (p + 1)) < K)%nat ->
      0 <= o -> o <= p -> p + 1 <= len -> inv buf m (p + 1) ->
      evt bsegs POST (ST 0x850a4 m x8 x9 (Z_to_bv 64 (A + o)) x11 (Z_to_bv 64 (A + p)) x13 x18 x19 x20).
    Proof.
      induction kk as [|kk IHkk]; intros p o buf m x8 x9 x11 x13 x18 x19 x20 Hkk HK Ho Hop Hp INV; inv_parts INV; lits. bandM. sepM.
      all: zstep; replace (A + p + 1) with (A + (p + 1)) by lia.
      all: zstep; zstep; chk INV (p + 1).
      all: rd INV (p + 1) cb.
      all: zstep; cbv beta; zstep; zstep; replace (A + o + 1) with (A + (o + 1)) by lia; if_cases Kz; zify_cond Kz.
      all: lazymatch goal with
           | Kz' : bv_unsigned _ = 0 |- _ => zstep; zstep; apply (IH (p + 1) (o + 1) buf m); [lia| lia| lia| exact INV]   (* [comment removed for export] *)
           | |- _ => idtac end.
      { exfalso. pose proof (proj2 Hzcb ltac:(lia)). lia. }
      assert (Hpl : p + 1 < len) by lia.
      (* [comment removed for export] *)
      zstep. zstep. chk INV (o + 1).
      do_store (o + 1) cb ltac:(symmetry; apply le1_zxb).
      mk_inv INV1 (p + 1). { apply sufx_upd; [exact SX| lia|]. destruct (Z.eq_dec (o + 1) (p + 1)) as [E|]; [right; rewrite E; exact Hncb| left; lia]. }
      clear SX INV. inv_parts INV1.
      (* [comment removed for export] *)
      chk INV1 (p + 1).
      rd INV1 (p + 1) cb1. rewrite Hncb in Hncb1. injection Hncb1 as <-. clear Hzcb1.
      zstep. cbv beta. zstep. if_cases Kbs; zify_cond Kbs.
      - (* [comment removed for export] *)
        zstep. if_cases Kq; zify_cond Kq.
        + (* [comment removed for export] *)
          chk INV1 (o + 1).
          zstep. replace (A + (p + 1) + 1) with (A + (p + 2)) by lia.
          do_store (o + 1) (wb 34) ltac:(apply byte_list_eq; reflexivity).
          mk_inv INV2 (p + 2). { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia| left; lia]. }
          guard1. zstep. replace (A + (o + 1) + 1) with (A + (o + 2)) by lia. guard1.
          zstep. replace (A + p + 2) with (A + (p + 2)) by lia. zstep. replace (A + o + 2) with (A + (o + 2)) by lia. zstep.
          eapply (IH (p + 2) (o + 2)); [lia| lia| lia| exact INV2].
        + (* [comment removed for export] *)
          mk_inv INV2 (p + 2). { eapply sufx_mono; [exact SX| lia]. }
          zstep. zstep.
          zstep. replace (A + (p + 1) + 1) with (A + (p + 2)) by lia. guard1.
          zstep. replace (A + (o + 1) + 1) with (A + (o + 2)) by lia. guard1.
          eapply (IHkk (p + 1) (o + 1)); [lia| lia| lia| lia| lia| replace (p + 1 + 1) with (p + 2) by lia; exact INV2].
      - (* [comment removed for export] *)
        guard1.
        zstep. replace (A + p + 2) with (A + (p + 2)) by lia.
        zstep. zstep. chk INV1 (p + 2).
        rd INV1 (p + 2) c2.
        zstep. cbv beta. zstep. if_cases Kq2; zify_cond Kq2.
        + (* [comment removed for export] *)
          mk_inv INV2 (p + 2). { eapply sufx_mono; [exact SX| lia]. }
          zstep. zstep.
          zstep. replace (A + (p + 1) + 1) with (A + (p + 2)) by lia. guard1.
          zstep. replace (A + (o + 1) + 1) with (A + (o + 2)) by lia. guard1.
          eapply (IHkk (p + 1) (o + 1)); [lia| lia| lia| lia| lia| replace (p + 1 + 1) with (p + 2) by lia; exact INV2].
        + (* [comment removed for export] *)
          assert (Ec2 : c2 = wb 34) by (eapply orig_nth_val; [exact Hnc2| exact Kq2]).
          zstep. replace (A + (o + 1) + 1) with (A + (o + 2)) by lia. guard1.
          zstep. replace (A + o + 2) with (A + (o + 2)) by lia.
          zstep. zstep. chk INV1 (o + 2).
          zstep. replace (A + (p + 1) + 1) with (A + (p + 2)) by lia.
          do_store (o + 2) (wb 34) ltac:(apply byte_list_eq; reflexivity).
          mk_inv INV2 (p + 3).
          { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia|].
            destruct (Z.eq_dec (o + 2) (p + 2)) as [E|NE]; [right; rewrite E, Hnc2, Ec2; reflexivity| left; lia]. }
          guard2.
          zstep. replace (A + (p + 2) + 1) with (A + (p + 3)) by lia. guard1.
          zstep. replace (A + (o + 2) + 1) with (A + (o + 3)) by lia. guard1.
          eapply (IHkk (p + 2) (o + 2)); [lia| lia| lia| lia| lia| replace (p + 2 + 1) with (p + 3) by lia; exact INV2].
    Qed.

    (* [comment removed for export] *)
    Lemma l_string : forall j i buf m x8 x9 x11 x18 x19 x20,
      (Z.to_nat (len - j) <= K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      nth_error orig (Z.to_nat j) = Some (wb 34) ->
      evt bsegs POST (ST 0x85068 m x8 x9 (Z_to_bv 64 (A + i)) x11 (Z_to_bv 64 (A + j)) (Z_to_bv 64 34) x18 x19 x20).
    Proof.
      intros j i buf m x8 x9 x11 x18 x19 x20 HK Hij Hj INV Hb. inv_parts INV. lits. bandM. sepM.
      zstep. zstep. chk INV i.
      zstep. replace (A + j + 1) with (A + (j + 1)) by lia.
      do_store i (wb 34) ltac:(apply byte_list_eq; reflexivity).
      mk_inv INV1 (j + 1).
      { apply sufx_upd; [eapply sufx_mono; [exact SX| lia]| lia|]. destruct (Z.eq_dec i j) as [->|]; [right; exact Hb| left; lia]. }
      guard2.
      zstep. replace (A + i + 1) with (A + (i + 1)) by lia. guard1.
      eapply (sl_loop (Z.to_nat (len - (j + 1))) j i); [lia| lia| lia| lia| lia| exact INV1].
    Qed.

    (* [comment removed for export] *)
    Ltac inv_at q :=
      lazymatch goal with ARR : u8arr bsegs ?mc A ?buf, SX : sufx _ ?buf _ |- _ =>
        assert (inv buf mc q);
        [ split; [exact ARR|]; split; [eapply sufx_mono; [exact SX| lia]| split; [assumption| split; [assumption| split; [assumption| split; [assumption| assumption]]]]] |]
      end.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma ol_loop : forall (kk : nat) q i buf m x8 x9 x13 x18 x19 x20,
      (Z.to_nat (len - q) <= kk)%nat -> (Z.to_nat (len - q) < K)%nat ->
      0 <= i <= q -> q <= len -> inv buf m q ->
      evt bsegs POST (ST 0x851d8 m x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + q)) (Z_to_bv 64 (A + q)) x13 x18 x19 x20).
    Proof.
      induction kk as [|kk IHkk]; intros q i buf m x8 x9 x13 x18 x19 x20 Hkk HK Hiq Hq INV; inv_parts INV; lits; rd INV q cb.
      all: zstep; cbv beta; zstep; if_cases Kz; zify_cond Kz; [apply (IH q i buf m); [lia| lia| lia| exact INV]|].
      { exfalso. pose proof (proj2 Hzcb ltac:(lia)). lia. }
      inv_at (q + 1). rename H into INV1.
      zstep. if_cases Knl; zify_cond Knl.
      - (* [comment removed for export] *)
        guard1. zstep. replace (A + q + 1) with (A + (q + 1)) by lia. zstep.
        apply (IH (q + 1) i buf m); [lia| lia| lia| exact INV1].
      - (* [comment removed for export] *)
        guard1. zstep. zstep. replace (A + q + 1) with (A + (q + 1)) by lia. zstep. zstep. chk INV1 (q + 1).
        apply (IHkk (q + 1) i buf m); [lia| lia| lia| lia| exact INV1].
    Qed.

    (* [comment removed for export] *)
    Lemma ml_loop : forall (kk : nat) q i buf m x8 x9 x13 x18 x19 x20,
      (Z.to_nat (len - q) <= kk)%nat -> (Z.to_nat (len - q) < K)%nat ->
      0 <= i <= q -> q <= len -> inv buf m q ->
      evt bsegs POST (ST 0x85230 m x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + q)) (Z_to_bv 64 (A + q)) x13 x18 x19 x20).
    Proof.
      induction kk as [|kk IHkk]; intros q i buf m x8 x9 x13 x18 x19 x20 Hkk HK Hiq Hq INV; inv_parts INV; lits; rd INV q cb.
      all: zstep; cbv beta; zstep; if_cases Kst; zify_cond Kst.
      (* [comment removed for export] *)
      1:{ exfalso. pose proof (proj2 Hzcb ltac:(lia)). lia. }
      1:{ zstep. if_cases Kz; zify_cond Kz; [exfalso; pose proof (proj2 Hzcb ltac:(lia)); lia|]. zstep. apply (IH q i buf m); [lia| lia| lia| exact INV]. }
      2:{ (* [comment removed for export] *)
          zstep. if_cases Kz; zify_cond Kz.
          - inv_at (q + 1). rename H into INV1.
            zstep. replace (A + q + 1) with (A + (q + 1)) by lia. guard1. zstep. replace (A + q + 1) with (A + (q + 1)) by lia.
            zstep. zstep. chk INV1 (q + 1).
            apply (IHkk (q + 1) i buf m); [lia| lia| lia| lia| exact INV1].
          - zstep. apply (IH q i buf m); [lia| lia| lia| exact INV]. }
      (* [comment removed for export] *)
      guard1. zstep. replace (A + q + 1) with (A + (q + 1)) by lia. zstep. zstep. chk INV (q + 1).
      rd INV (q + 1) c2.
      replace (wa (A + (q + 1))) with (Z_to_bv 64 (A + q + 1)) in RD0 by (unfold wa; f_equal; lia).
      zstep. cbv beta. zstep. if_cases Ksl; zify_cond Ksl.
      + (* [comment removed for export] *)
        inv_at (q + 2). rename H into INV2.
        guard1. zstep. replace (A + q + 2) with (A + (q + 2)) by lia. zstep.
        apply (IH (q + 2) i buf m); [lia| lia| lia| exact INV2].
      + (* [comment removed for export] *)
        inv_at (q + 1). rename H into INV1.
        zstep. replace (A + q + 1) with (A + (q + 1)) by lia. guard1. zstep. replace (A + q + 1) with (A + (q + 1)) by lia.
        zstep. zstep. chk INV1 (q + 1).
        apply (IHkk (q + 1) i buf m); [lia| lia| lia| lia| exact INV1].
    Qed.

    (* [comment removed for export] *)
    Lemma l_slash : forall j i buf m x8 x9 x11 x13 x18 x19 x20,
      (Z.to_nat (len - j) <= K)%nat -> 0 <= i <= j -> j < len -> inv buf m j ->
      evt bsegs POST (ST 0x85198 m x8 x9 (Z_to_bv 64 (A + i)) x11 (Z_to_bv 64 (A + j)) x13 x18 x19 x20).
    Proof.
      intros j i buf m x8 x9 x11 x13 x18 x19 x20 HK Hij Hj INV. inv_parts INV. lits. bandM. sepM.
      guard1. zstep. replace (A + j + 1) with (A + (j + 1)) by lia. zstep. zstep. chk INV (j + 1).
      rd INV (j + 1) c1.
      zstep. cbv beta. zstep. if_cases Kst; zify_cond Kst.
      - (* [comment removed for export] *)
        inv_at (j + 2). rename H into INV2.
        zstep. replace (A + j + 2) with (A + (j + 2)) by lia. guard1. zstep. zstep. zstep. chk INV2 (j + 2).
        apply (ml_loop (Z.to_nat (len - (j + 2))) (j + 2) i buf m); [lia| lia| lia| lia| exact INV2].
      - zstep. if_cases Ksl; zify_cond Ksl.
        + (* [comment removed for export] *)
          inv_at (j + 1). rename H into INV1.
          apply (IH (j + 1) i buf m); [lia| lia| lia| exact INV1].
        + (* [comment removed for export] *)
          inv_at (j + 2). rename H into INV2.
          zstep. replace (A + j + 2) with (A + (j + 2)) by lia. guard1. zstep. zstep. zstep. chk INV2 (j + 2).
          apply (ol_loop (Z.to_nat (len - (j + 2))) (j + 2) i buf m); [lia| lia| lia| lia| exact INV2].
    Qed.

    (* [comment removed for export] *)
    Ltac dispatch :=
      zstep; zstep; step; try rewrite sx32_lit by lia; zstep; step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity])
      | _ => idtac
      end.

    (* [comment removed for export] *)
    Lemma l_head : forall j i buf m x8 x9 x12 x13 x18 x19 x20,
      (Z.to_nat (len - j) = K) -> 0 <= i <= j -> j <= len -> inv buf m j ->
      evt bsegs POST (ST 0x85038 m x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x12 x13 x18 x19 x20).
    Proof.
      intros j i buf m x8 x9 x12 x13 x18 x19 x20 HK Hij Hj INV. inv_parts INV. lits. bandM. sepM.
      zstep. zstep. zstep. chk INV j.
      rd INV j cb.
      zstep. cbv beta. zstep. if_cases Kbig; zify_cond Kbig.
      { (* [comment removed for export] *) eapply l_default; [lia| lia| lia| exact INV| exact Hncb]. }
      destruct (Z.eq_dec (bv_unsigned cb) 0) as [E0|N0].
      { (* [comment removed for export] *) rewrite E0. unfold MJT. dispatch. eapply (l_nul j i); [lia| lia| exact INV]. }
      assert (Hjl : j < len) by lia.
      destruct (Z.eq_dec (bv_unsigned cb) 34) as [E34|N34].
      { rewrite E34. unfold MJT. dispatch. eapply l_string; [lia| lia| lia| exact INV|]. rewrite Hncb. f_equal. eapply orig_nth_val; [exact Hncb| exact E34]. }
      destruct (Z.eq_dec (bv_unsigned cb) 47) as [E47|N47].
      { rewrite E47. unfold MJT. dispatch. eapply l_slash; [lia| lia| lia| exact INV]. }
      assert (WS : forall c xa1, c = 9 \/ c = 10 \/ c = 13 \/ c = 32 -> bv_unsigned cb = c ->
                evt bsegs POST (ST 0x85054 m x8 x9 (Z_to_bv 64 (A + i)) xa1 (Z_to_bv 64 (A + j)) (Z_to_bv 64 (bv_unsigned cb)) x18 x19 x20)).
      { intros c xa1 Hc E. rewrite E. unfold MJT. destruct Hc as [->|[->|[->| ->]]]; dispatch; (eapply l_ws; [lia| lia| lia| exact INV]). }
      destruct (Z.eq_dec (bv_unsigned cb) 9) as [E|N9]; [apply (WS 9); [tauto| exact E]|].
      destruct (Z.eq_dec (bv_unsigned cb) 10) as [E|N10]; [apply (WS 10); [tauto| exact E]|].
      destruct (Z.eq_dec (bv_unsigned cb) 13) as [E|N13]; [apply (WS 13); [tauto| exact E]|].
      destruct (Z.eq_dec (bv_unsigned cb) 32) as [E|N32]; [apply (WS 32); [tauto| exact E]|].
      clear WS.
      pose proof (jt_read m (bv_unsigned cb) MI ltac:(lia)) as RT.
      rewrite (jt_sel_default (bv_unsigned cb)) in RT by assumption.
      unfold MJT in *. dispatch. eapply l_default; [lia| lia| lia| exact INV| exact Hncb].
    Qed.
  End Head.

  (* [comment removed for export] *)
  Lemma head_all : forall (K : nat) j i buf m x8 x9 x12 x13 x18 x19 x20,
    (Z.to_nat (len - j) = K) -> 0 <= i <= j -> j <= len -> inv buf m j ->
    evt bsegs POST (ST 0x85038 m x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + j)) x12 x13 x18 x19 x20).
  Proof.
    induction K as [K IHK] using lt_wf_ind. apply l_head.
    intros j i buf m x8 x9 x12 x13 x18 x19 x20 HK Hij Hj INV. eapply (IHK (Z.to_nat (len - j))); [exact HK| reflexivity| exact Hij| exact Hj| exact INV].
  Qed.
End Proofs.

Lemma minify_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A lo : Z) (s : list byte),
  a0 = wz A ->
  u8arr bsegs m A (s ++ [wb 0]) ->
  ~ In (wb 0) s ->
  AIMG_HI <= A -> A + Z.of_nat (length s) + 1 <= alloc_ceiling ->
  shbase_cells m -> text_sh m A (Z.of_nat (length s) + 1) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + MINIFY_STACK <= bv_unsigned sp ->
  sclr A (Z.of_nat (length s) + 1) ->           (* [comment removed for export] *)
  evt bsegs (minify_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A (S (length s)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MINIFY_ENTRY) fc None m (seg_rom bsegs)).
Proof.
  intros until s. intros A0 ARR NONUL AH AC SB TS MI ST LOC LOR ABND. pose proof ABND as ABND'. sclr_lits ABND'. unfold wz in A0. subst a0. unfold MINIFY_ENTRY, MINIFY_STACK in *.
  pose proof (u8arr_bound _ _ _ _ ARR) as ABd. rewrite length_app in ABd. cbn [length] in ABd.
  pose proof AH as AH'. pose proof AC as AC'. pose proof LOC as LOC'. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AH'. bandM. sepM. try rewrite alloc_ceiling_eq in AC', LOC'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(A, A + Z.of_nat (S (length s))); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof SB as SB0. shbase_split SB0.
  carve_frame 48%nat ST.
  do 7 zstep.                                              (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold minify_post. nexists 15%nat. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    exists (s ++ [wb 0]). split; [exact ARR|]. split; [rewrite length_app; cbn; lia|]. apply in_or_app. right. left. reflexivity.
  - do 17 zstep.
    eapply evt_eq.
    2:{ eapply (head_all ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A lo s NONUL ltac:(split; assumption) ltac:(split; [exact LOC| lia]) TS ABND
                 (Z.to_nat (Z.of_nat (length s) - 0)) 0 0 (s ++ [wb 0])); [reflexivity| lia| lia|].
        split; [eassumption|]. split; [apply sufx_refl|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR]. }
    unfold mkR. rewrite Z.add_0_r.
    replace (Z_to_bv 64 (-1) : word) with (Z_to_bv 64 18446744073709551615 : word) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 (-3) : word) with (Z_to_bv 64 18446744073709551613 : word) by (apply bv_eq; reflexivity).
    reflexivity.
Qed.


End CeilWrap.
End CJ_minify.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv CJ_traces ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_fuzz_iface.
Import CJ_delete.
Import CJ_minify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_mem2 RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nul_split : forall (l : list byte), In (wb 0) l -> exists str rest, l = str ++ wb 0 :: rest /\ ~ In (wb 0) str.
Proof.
  induction l as [|b l IH]; intros Hin; [destruct Hin|].
  destruct (base.decide (b = wb 0)) as [->|NE].
  - exists [], l. split; [reflexivity| intros []].
  - destruct Hin as [E|Hin]; [exfalso; exact (NE E)|]. (nelim (IH Hin) 4%nat; intros str rest -> NN).
    exists (b :: str), rest. split; [reflexivity|]. intros [E|H]; [exact (NE E)| exact (NN H)].
Qed.

Lemma split4 : forall (data : list byte), (4 <= length data)%nat ->
  data = firstn 4 data ++ skipn 4 data /\ length (firstn 4 data) = 4%nat.
Proof. intros data H. split; [symmetry; apply firstn_skipn| rewrite firstn_length; lia]. Qed.

Lemma u8arr_mid : forall m A l1 l2 l3,
  u8arr bsegs m A (l1 ++ l2 ++ l3) -> u8arr bsegs m (A + Z.of_nat (length l1)) l2.
Proof.
  intros m A l1 l2 l3 [BY (W0 & W1 & WR)]. rewrite !length_app in W1, WR.
  apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _].
  split; [exact BY|]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + Z.of_nat (length l1) + i) with (A + (Z.of_nat (length l1) + i)) by lia. apply WR. lia.
Qed.

Lemma copy_text_u8arr : forall m C n pre str rest,
  rw_cells bsegs m C [CB n (pre ++ str ++ wb 0 :: rest)] -> length pre = 4%nat ->
  u8arr bsegs m (C + 4) (str ++ [wb 0]).
Proof.
  intros m C n pre str rest H L. apply u8arr_of_rw_cells in H.
  replace (pre ++ str ++ wb 0 :: rest) with (pre ++ (str ++ [wb 0]) ++ rest) in H by (rewrite <- !app_assoc; reflexivity).
  apply u8arr_mid in H. rewrite L in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma dpres_of_cj_pres : forall sp0 LB SP m m', cj_pres sp0 LB [] SP m m' -> dpres sp0 LB [] SP m m'.
Proof. intros sp0 LB SP m m' H a Ha [Hc _]. apply H; assumption. Qed.

Lemma dpres_weaken : forall sp0 LB LB' SP SP' m m',
  dpres sp0 LB [] SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> dpres sp0 LB' [] SP' m m'.
Proof.
  intros sp0 LB LB' SP SP' m m' H HS HL. eapply magree_mono; [exact H|]. cbv beta.
  intros a [Hc Hn]. split; [|exact Hn].
  destruct Hc as [Hc|[Hc|[(A & n & Hb & Hr)|[(Fr & k & Hb & Hr)|Hc]]]]; [left; lia| right; left; exact Hc| right; right; left| destruct Hb| do 4 right; exact Hc].
  exists A, n. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma dpres_rw_cells_stack : forall sp0 LB SP m m' A cs,
  dpres sp0 LB [] SP m m' -> rw_cells bsegs m A cs -> SP <= A -> A + Z.of_nat (cells_size cs) <= sp0 + 4096 -> alloc_ceiling <= SP ->
  rw_cells bsegs m' A cs.
Proof.
  intros sp0 LB SP m m' A cs HP H HS HA HC. try rewrite alloc_ceiling_eq in HC.
  eapply rw_cells_magree; [exact HP| exact H|]. intros a Ha. split; [left; lia|]. unfold AERRNO, ATP, AGERROR0, AGERROR1. lia.
Qed.

Lemma dpres_bytes_at_block : forall sp0 LB SP m m' D n bs,
  ablock_range D n -> In (D, n) LB ->
  dpres sp0 LB [] SP m m' -> bytes_at bsegs m D bs -> Z.of_nat (length bs) <= n -> bytes_at bsegs m' D bs.
Proof.
  intros sp0 LB SP m m' D n bs HR HD HP BY LEN. (nelimp HR 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
  eapply bytes_at_magree; [exact HP| exact BY|]. intros a Ha. split.
  - right; right; left. exists D, n. split; [exact HD| lia].
  - unfold AERRNO, ATP, AGERROR0, AGERROR1. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_zero_stack_pres : forall sp0 LB SP m m',
  dpres sp0 LB [] SP m m' -> sh_zero m alloc_ceiling (2^47) -> sh_zero m' alloc_ceiling (2^47).
Proof.
  intros sp0 LB SP m m' HP H. eapply sh_zero_ext; [exact H|]. intros j Hj.
  assert (R : SH alloc_ceiling <= j < SH (2^47)).
  { unfold SH, SHADOW_OFFSET in *. rewrite ?alloc_ceiling_eq in *. Z.div_mod_to_equations. lia. }
  pose proof R as R'. unfold SH, SHADOW_OFFSET in R'. rewrite ?alloc_ceiling_eq in R'.
  apply HP; [Z.div_mod_to_equations; lia|].
  split; [do 4 right; exact R|]. unfold AERRNO, ATP, AGERROR0, AGERROR1. Z.div_mod_to_equations. lia.
Qed.

Lemma sh_zero_stack_munch : forall W m m',
  sh_zero m alloc_ceiling (2^47) -> munch W m m' -> Forall (fun iv => sclr (fst iv) (snd iv - fst iv)) W -> sh_zero m' alloc_ceiling (2^47).   (* [comment removed for export] *)
Proof.
  intros W m m' H MU HW.
  eapply sh_zero_munch; [exact H| exact MU| unfold SH, SHADOW_OFFSET; try rewrite alloc_ceiling_eq; Z.div_mod_to_equations; lia
                       | unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia|].
  clear H MU. induction W as [|[u v] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [fst snd] in H1.
  split; [| apply IH; exact H2]. clear IH H2. (nelimp SH_ceiling_bounds 3%nat; intros SHC1 SHC2 SHC3).
  assert (E47 : SH (2 ^ 47 - 1) + 1 = KHIGHMEM_BEG) by reflexivity. rewrite E47. clear E47.
  unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *. destruct H1 as [H1|H1]; [right| left]; lia.
Qed.

(* [comment removed for export] *)
Lemma dpres_munch : forall sp0 LB SP m m1 m2 lo1 hi1 lo2 hi2,
  dpres sp0 LB [] SP m m1 -> munch [(lo1, hi1); (lo2, hi2)] m1 m2 -> wmono bsegs m1 m2 ->
  AIMG_HI <= lo1 -> hi1 <= alloc_ceiling -> (forall A n, In (A, n) LB -> A + n <= lo1 \/ hi1 <= A) ->
  alloc_ceiling <= lo2 -> hi2 <= SP -> alloc_ceiling <= SP ->
  (forall A n, In (A, n) LB -> A + n <= alloc_ceiling) ->
  sclr lo1 (hi1 - lo1) ->                       (* [comment removed for export] *)
  dpres sp0 LB [] SP m m2.
Proof.
  intros sp0 LB SP m m1 m2 lo1 hi1 lo2 hi2 HP MU WM L1 H1 B1 L2 H2 HSP BL SC.
  eapply dpres_trans; [exact HP|]. eapply magree_of_munch; [exact MU| exact WM|].
  intros a Ha [Hc _]. try rewrite alloc_ceiling_eq in H1, L2, HSP, BL. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *.
  enough (G : ~ (lo1 <= a < hi1) /\ ~ (lo2 <= a < hi2)) by (destruct G as [G1 G2]; cbn; split; [exact G1| split; [exact G2| exact I]]).
  destruct Hc as [Hs|[Hi|[(A & n & Hb & Hr)|[(Fr & k & Hb & _)|Hsh]]]].
  - lia.
  - pose proof (aclient_image_lt a Hi). lia.
  - pose proof (B1 A n Hb). pose proof (BL A n Hb). lia.
  - destruct Hb.
  - pose proof (stack_sh_in_band _ _ Hsh) as AB. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in AB. bandM. sepM. lia.
Qed.

(* [comment removed for export] *)
Lemma fuzz_budget : forall size blen, 5 <= size -> 1 <= blen <= size - 4 ->
  pdoc_cost blen + PRINT_COST + cost_free + cost_malloc size + cost_free + cost_free * (blen + 1) <= FUZZ_COST size.
Proof.
  intros size blen HS HB. unfold FUZZ_COST, pdoc_cost, pv_cost_pre, PV_FRATE, PV_RATE. rewrite cost_free_eq.
  (* [comment removed for export] *)
  destruct (is_cl24 size) eqn:C24.
  - pose proof (RT_cost.is_cl24_range size ltac:(lia) C24). pose proof (RT_cost.cost_malloc_lin size ltac:(lia)). lia.
  - pose proof (RT_cost.cost_malloc_le13_noncl24 size ltac:(lia) C24). lia.
Qed.

Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK, DELETE_STACK, APRINT_STACK, APV_STACK, AMALLOC_STACK, AINTRIN_STACK, MINIFY_STACK in *; lia | sclr_tac2 ].
(* [comment removed for export] *)
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).

(* [comment removed for export] *)
Section S.
  Variables (AI : art_iface) (TI : trs_iface) (S_LIB : list (list Z)).
  Hypothesis PARSE : parse_wopts_stmt AI TI.
  Hypothesis PRB : pbuffered_stmt AI TI.
  Hypothesis PRF : cjprint_stmt AI TI.
  Hypothesis PRU : cjprintu_stmt AI TI.
  Hypothesis MEMCPY : asan_memcpy_spec.
  (* [comment removed for export] *)
  Hypothesis LIBF : forall tr, In tr (S_FUZZ ++ S_PARSE RA_PWLO ++ S_DELETE ++ S_PRINT_CONST) -> In tr S_LIB.

  Section Body.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
              (m0 : word -> option byte) (g0 : lghost) (sp0 SPB : Z) (LB : list cblock) (TRS0 : list (list Z)) (B0 np0 : Z)
              (D size : Z) (data : list byte) (lo : Z).
    Hypothesis STATL : forall tr, In tr S_LIB -> STAT TI tr.
    Hypothesis SPB1 : bv_unsigned sp <= SPB.
    Hypothesis SPB2 : SPB < 2^62.
    Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
    Hypothesis SP0 : sp0 <= 2^47.
    Hypothesis TOP : bv_unsigned sp + 16 <= ASTACK_TOP sp0.
    Hypothesis SPS0 : bv_unsigned sp + 16 <= sp0.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis BOT : ASTACK_BOTTOM sp0 <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - AFUZZ_STACK.
    Hypothesis TP : tp = wz ATP.
    Hypothesis SZ : 0 <= size < 2^26.
    Hypothesis NPM : np0 + FUZZ_NP size <= NPMAX TI.
    Hypothesis HB0 : FUZZ_COST size <= B0.

    Notation SPF := (bv_unsigned sp + -64).
    Notation POST := (llvmfuzz_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB TRS0 B0 np0 D size data lo m0 g0).
    Notation FRAME mm fj := (rw_cells bsegs mm (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    (* [comment removed for export] *)
    Notation LST pc Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 :=
      (MS (mkR rav (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          Fv (Z_to_bv 64 pc) fcv None mm (seg_rom bsegs)).

    (* [comment removed for export] *)
    Definition linv (LBX : list cblock) (TRSX : list (list Z)) (BX npX : Z) (mm : word -> option byte) (mo : Model) (g : lghost)
        (fj : list byte) (Fv : bvmap 5 word) (fcv : bv 32) : Prop :=
      ART AI sp0 SPB LBX [] TRSX BX mm mo g /\ stk bsegs mm lo SPF /\ FRAME mm fj
      /\ (exists e, rw_cells bsegs mm AERRNO [C4 e]) /\ mem_inv bsegs mm
      /\ dpres sp0 LB [] (bv_unsigned sp) m0 mm /\ frm0 fcv /\ (forall k : bv 5, fp_callee_saved k -> reg_get Fv k = reg_get F k)
      /\ gmono g0 g /\ TINV TI npX TRSX /\ np0 <= npX <= np0 + FUZZ_NP size
      /\ sh_zero mm alloc_ceiling (2^47)
      /\ (size <= 4 \/ (ablock_range D size /\ In (D, size) LB /\ bytes_at bsegs mm D data /\ Z.of_nat (length data) = size)).

    Lemma SPFeq : bv_unsigned (Z_to_bv 64 SPF) = SPF.
    Proof. apply unsigned_lit. alia. Qed.
    Lemma SPFal : SPF mod 16 = 0.
    Proof. replace SPF with (bv_unsigned sp - 64) by lia. rewrite Zminus_mod, SPAL. reflexivity. Qed.
    Lemma SPtop : bv_unsigned sp + 16 <= sp0 + 4096.
    Proof. clear -TOP. unfold ASTACK_TOP, roundup in TOP. Z.div_mod_to_equations. lia. Qed.
    Lemma SPhi : bv_unsigned sp < 2^64.
    Proof. pose proof (bv_unsigned_in_range 64 sp) as H. change (bv_modulus 64) with (2^64) in H. lia. Qed.

    (* [comment removed for export] *)
    Lemma st_fuzz : Forall (STAT TI) S_FUZZ.
    Proof. apply Forall_forall. intros tr H. apply STATL, LIBF. apply in_or_app. left. exact H. Qed.
    Lemma st_free1 : STAT TI [PC0_FREE; 0x8252c].
    Proof. exact (Forall_inv st_fuzz). Qed.
    Lemma st_malloc : STAT TI [PC0_MALLOC; 0x8253c].
    Proof. exact (Forall_inv (Forall_inv_tail st_fuzz)). Qed.
    Lemma st_free2 : STAT TI [PC0_FREE; 0x82568].
    Proof. exact (Forall_inv (Forall_inv_tail (Forall_inv_tail st_fuzz))). Qed.
    Lemma st_delete : Forall (STAT TI) S_DELETE.
    Proof. apply Forall_forall. intros tr H. apply STATL, LIBF. do 2 (apply in_or_app; right). apply in_or_app; left. exact H. Qed.
    Lemma st_print : Forall (STAT TI) S_PRINT_CONST.
    Proof. apply Forall_forall. intros tr H. apply STATL, LIBF. do 3 (apply in_or_app; right). exact H. Qed.
    Lemma st_parse : forall tr, In tr (S_PARSE RA_PWLO) -> STAT TI tr.
    Proof. intros tr H. apply STATL, LIBF. apply in_or_app; right. apply in_or_app; left. exact H. Qed.
    Lemma st_pwlo_head : STAT TI [PC0_MALLOC; 0x829e8; RA_PWLO].
    Proof. apply st_parse. left. reflexivity. Qed.
    Lemma st_pv_pwlo : forall site b, In site PWLO_PV_RAS -> STAT TI (tr_pv_pwlo_at site RA_PWLO b).
    Proof. intros site b H. apply st_parse, In_S_PARSE_pwlo_at. exact H. Qed.
    Lemma st_pv_pobj : forall b, STAT TI (tr_pv_pobj b).
    Proof. intros b. apply st_parse. apply In_S_PARSE_pobj. Qed.
    Lemma st_parse_const_delete : Forall (STAT TI) (S_PARSE_CONST ++ S_DELETE).
    Proof.
      apply Forall_app. split; [| exact st_delete]. apply Forall_forall. intros tr H. apply st_parse. right. apply in_or_app. left. exact H.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_ret : forall LBX LX TRSX BX npX mm mo g fj Fv fcv rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
      linv LBX TRSX BX npX mm mo g fj Fv fcv -> Permutation LBX (LB ++ LX) -> B0 - FUZZ_COST size <= BX ->
      LSCPS bsegs POST (LST 0x82570 Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros (HL & ST & FR & [e ERR] & MI & PR & FRM & FA & GM & TV & NP & SSZ & DAT) HP HB.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      eapply lscps_step_evt. cbv beta delta [mkR].
      do 10 zstep.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply lscps_done. unfold llvmfuzz_post.
      nexists 24%nat. split; [reflexivity|].
      split; [reflexivity|]. split; [exact FRM|]. split; [exact FA|]. split; [exact MI|]. split; [exact ST|].
      split; [exact ERR|]. split; [exact HL|]. split; [exact HP|]. split; [exact PR|]. split; [exact GM|].
      split; [exact TV|]. split; [exact NP|]. split; [exact HB|]. split; [exact SSZ|].
      destruct DAT as [H|(_ & _ & H & _)]; [left; exact H| right; exact H].
    Qed.

    (* [comment removed for export] *)
    Lemma linv_xfer : forall LBX TRSX BX npX mm mo g fj Fv fcv LBY mm' mo' g' LBX' TRSX' BX' npX' e' Fv' fcv',
      linv LBX TRSX BX npX mm mo g fj Fv fcv ->
      cj_pres sp0 LBY [] SPF mm mm' -> (forall b, In b LB -> In b LBY) ->
      ART AI sp0 SPB LBX' [] TRSX' BX' mm' mo' g' -> stk bsegs mm' lo SPF -> rw_cells bsegs mm' AERRNO [C4 e'] -> mem_inv bsegs mm' ->
      gmono g g' -> TINV TI npX' TRSX' -> np0 <= npX' <= np0 + FUZZ_NP size ->
      frm0 fcv' -> (forall k : bv 5, fp_callee_saved k -> reg_get Fv' k = reg_get Fv k) ->
      linv LBX' TRSX' BX' npX' mm' mo' g' fj Fv' fcv'.
    Proof.
      intros until fcv'. intros (HL & ST & FR & _ & MI & PR & FRM & FA & GM & TV & NP & SSZ & DAT) PRS0 HLL HL' ST' ERR' MI' GM' TV' NP' FRM' FA'.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPtop as SPT.
      assert (PRS : cj_pres sp0 LB [] SPF mm mm') by (eapply cj_pres_weaken; [exact PRS0| lia| exact HLL| intros f Hf; exact Hf]).
      split; [exact HL'|]. split; [exact ST'|]. split.
      { eapply cj_pres_rw_cells; [exact PRS| exact FR| left; cbn; lia]. }
      split; [exists e'; exact ERR'|]. split; [exact MI'|]. split.
      { eapply dpres_trans; [exact PR|]. apply dpres_of_cj_pres. eapply cj_pres_weaken; [exact PRS| lia| intros b Hb; exact Hb| intros f Hf; exact Hf]. }
      split; [exact FRM'|]. split; [intros k Hk; rewrite (FA' k Hk); apply FA; exact Hk|].
      split; [eapply gmono_trans; [exact GM| exact GM']|]. split; [exact TV'|]. split; [exact NP'|]. split.
      { eapply sh_zero_stack_pres; [apply dpres_of_cj_pres; exact PRS| exact SSZ]. }
      destruct DAT as [H|(HR & HD & BY & LEN)]; [left; exact H| right]. split; [exact HR|]. split; [exact HD|]. split; [|exact LEN].
      eapply cj_pres_bytes_at; [exact PRS| exact BY|]. do 3 right; left. exists D, size. split; [exact HD| lia].
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_delete : forall LBX TRSX BX npX mm mo g fj Fv fcv (r : Z) (d : nat) (B : list cblock)
        rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
      linv LBX TRSX BX npX mm mo g fj Fv fcv -> Permutation (B ++ LB) LBX -> cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      B0 - FUZZ_COST size + cost_free * Z.of_nat (length B) <= BX ->
      LSCPS bsegs POST (LST 0x82568 Fv fcv mm rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 r) x19 x20 x21 x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros LI HP CH Hd HB. (nelimp LI 13%nat; intros HL ST FR [e ERR] MI PR FRM FA GM TV NP SSZ DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. pose proof SPtop as SPT. pose proof SPhi as SPH.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      assert (HBB : cost_free * Z.of_nat (length B) <= BX) by (rewrite cost_free_eq in *; lia).
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. change (Z_to_bv 64 534036) with (wz DELETE_ENTRY).
      apply evt_done. cbv beta.
      eapply lscps_bind.
      { pose proof (cjson_delete_spec AI TI d) as DS. unfold delete_spec_at in DS.
        eapply DS with (lo := lo) (LR := LB) (B := B) (T := CJ_PRINTABLE); clear DS; rewrite ?E1;
          first [ exact HL | exact CH | exact HP | exact ST | exact ERR | exact MI | exact TP | exact TV | exact st_delete | exact SP0 | reflexivity
                | exact HBB | exact AL | alia ]. }
      cbv beta. intros ms2 mo2 g2 PO.
      (nelim PO 27%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LR2 TRS2 -> MI2 ST2 ERR2 HL2 HP2 TV2 GM2 PR2)
.
      rewrite ?E1 in ST2, PR2.
      replace (ret_pc (Z_to_bv 64 0x82570)) with (Z_to_bv 64 0x82570) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply fuzz_ret with (LX := []).
      - eapply linv_xfer; [exact LI| exact PR2| intros b Hb; exact Hb| exact HL2| exact ST2| exact ERR2| exact MI2| exact GM2| exact TV2| exact NP| exact FRM| intros; reflexivity].
      - rewrite app_nil_r. exact HP2.
      - lia.
    Qed.

    Lemma blocks_apart : forall LBX TRSX BX mm mo g A n A' n',
      ART AI sp0 SPB LBX [] TRSX BX mm mo g -> In (A, n) LBX -> In (A', n') LBX -> A <> A' -> A + n <= A' \/ A' + n' <= A.
    Proof. intros until n'. intros HL H1 H2 NE. destruct (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ _ _ _ _ HL H1 H2 NE) as [K|K]; lia. Qed.

    (* [comment removed for export] *)
    Lemma fuzz_copy : forall LBX TRSX BX npX mm mo g fj Fv fcv (r : Z) (d : nat) (B : list cblock) (C : Z) (junk pre str rest : list byte)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31,
      linv ((C, size) :: LBX) TRSX BX npX mm mo g fj Fv fcv -> Permutation (B ++ LB) LBX -> cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      rw_cells bsegs mm C [CB (Z.to_nat size) junk] -> ~ In C (map fst LBX) ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      B0 - FUZZ_COST size + cost_free + cost_free * Z.of_nat (length B) <= BX ->
      LSCPS bsegs POST (LST 0x82540 Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) (Z_to_bv 64 C) x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) x19 x20 x21 x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros LI HP CH Hd BLK CN SZ4 DEQ LPRE NONUL HB.
      (nelimp LI 13%nat; intros HL ST FR [e ERR] MI PR FRM FA GM TV NP SSZ DAT).
      destruct DAT as [?|(DR & DIN & BY & LEN)]; [exfalso; lia|].
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. pose proof SPtop as SPT. pose proof SPhi as SPH.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity)) as CR.
      (nelimp CR 4%nat; intros C1 C2 C3 C4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
      (nelimp DR 4%nat; intros D1 D2 D3 D4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in D1. bandM. sepM. try rewrite alloc_ceiling_eq in D4.
      assert (DINX : In (D, size) LBX). { eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact DIN. }
      assert (CND : C <> D). { intros ->. apply CN. apply (in_map fst) in DINX. exact DINX. }
      pose proof (blocks_apart _ _ _ _ _ _ _ _ _ _ HL ltac:(left; reflexivity) ltac:(right; exact DINX) CND) as SEPCD.
      assert (XSEP : forall A' n', In (A', n') LBX -> C + size <= A' \/ A' + n' <= C).
      { intros A' n' HinX. eapply (blocks_apart _ _ _ _ _ _ _ _ _ _ HL); [left; reflexivity| right; exact HinX|].
        intros ->. apply CN. apply (in_map fst) in HinX. exact HinX. }
      assert (BSEP : forall A' n', In (A', n') B -> C + size <= A' \/ A' + n' <= C).
      { intros A' n' Hin. apply XSEP. eapply Permutation_in; [exact HP|]. apply in_or_app; left; exact Hin. }
      assert (LSEP : forall A' n', In (A', n') LB -> C + size <= A' \/ A' + n' <= C).
      { intros A' n' Hin. apply XSEP. eapply Permutation_in; [exact HP|]. apply in_or_app; right; exact Hin. }
      assert (LBLO : forall A' n', In (A', n') LB -> A' + n' <= alloc_ceiling).
      { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; eapply Permutation_in; [exact HP|]; apply in_or_app; right; exact Hin)) 4%nat; intros _ _ ? ?). lia. }
      assert (BLO : forall A' n', In (A', n') B -> AIMG_HI <= A' /\ A' + n' <= alloc_ceiling).
      { intros A' n' Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL ltac:(right; eapply Permutation_in; [exact HP|]; apply in_or_app; left; exact Hin)) 4%nat; intros ? _ ? ?). lia. }
      assert (LENN : length data = Z.to_nat size) by lia.
      unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      eapply evt_cut.
      { pose proof MEMCPY as MC. unfold asan_memcpy_spec, memcpy_contract in MC.
        eapply MC with (lo := lo) (d := C) (s := D) (n := size) (src := data) (junk := junk); clear MC; rewrite ?unsigned_lit by lia;
          first [ eapply (art_icpt_cells AI); exact HL | exact MI | exact ST | exact BY | exact LENN | exact BLK | reflexivity
                | app_rng0
                | apply wr_range_ok_high; lia
                | intros _; eapply art_block_shadow_ok; [exact HL| left; reflexivity]
                | intros _; eapply art_block_shadow_ok; [exact HL| right; exact DINX]
                | alia | lia ]. }
      cbv beta. intros ms3 PO3.
      (nelim PO3 22%nat; intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m3 -> MU3 WM3 MI3 BLK3 BY3 ST3).
      rewrite ?unsigned_lit in MU3, ST3 by lia. unfold AINTRIN_STACK in MU3.
      replace (ret_pc (Z_to_bv 64 0x82550)) with (Z_to_bv 64 0x82550) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (rw_cells_transport bsegs) in FR; [| exact MU3| exact WM3| cbn; lia].
      eapply (rw_cells_transport bsegs) in ERR; [| exact MU3| exact WM3| cbn; lia].
      assert (HL3 : ART AI sp0 SPB ((C, size) :: LBX) [] TRSX BX m3 mo g).
      { eapply (art_frame AI); [exact HL| exact MU3| exact WM3|].
        constructor; [| constructor; [| constructor]].
        - do 7 right. left. exists C, size. cbn. split; [left; reflexivity| lia].
        - right; left. cbn. lia. }
      pose proof (cj_chain_frame _ _ m3 _ _ _ _ CH MU3 WM3 ltac:(intros A' n' Hin; cbn; pose proof (BSEP A' n' Hin); pose proof (BLO A' n' Hin); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; lia)) as CH3.
      assert (PR3 : dpres sp0 LB [] (bv_unsigned sp) m0 m3).
      { eapply dpres_munch; [exact PR| exact MU3| exact WM3| unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| try rewrite alloc_ceiling_eq; lia| intros A' n' Hin; pose proof (LSEP A' n' Hin); lia| try rewrite alloc_ceiling_eq; lia| lia| lia| exact LBLO| sclr_tac2]. }
      assert (SSZ3 : sh_zero m3 alloc_ceiling (2^47)).
      { eapply sh_zero_stack_munch; [exact SSZ| exact MU3|]. constructor; [| constructor; [| constructor]]; cbn [fst snd]; sclr_tac2. }
      clear MU3 WM3 MI CH PR HL BLK BY SSZ ST.
      (* [comment removed for export] *)
      zstep. ugd.
      zstep. zstep.
      eapply evt_cut.
      { eapply (minify_spec) with (A := C + 4) (s := str) (lo := lo); rewrite ?unsigned_lit by lia;
          first [ reflexivity | exact NONUL | exact MI3 | exact ST3
                | eapply copy_text_u8arr; [| exact LPRE]; rewrite <- DEQ; exact BLK3
                | eapply art_shbase; exact HL3
                | eapply (art_text_sh AI); [exact HL3| left; reflexivity| lia| rewrite DEQ, !length_app in LEN; cbn [length] in LEN; lia]
                | rewrite DEQ, !length_app in LEN; cbn [length] in LEN; alia
                | alia ]. }
      cbv beta. intros ms4 PO4.
      (nelim PO4 22%nat; intros t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m4 -> MU4 WM4 MI4 ST4 _).
      rewrite ?unsigned_lit in MU4, ST4 by lia.
      replace (ret_pc (Z_to_bv 64 0x82560)) with (Z_to_bv 64 0x82560) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (SL : Z.of_nat (length str) + 5 + Z.of_nat (length rest) = size).
      { rewrite DEQ, !length_app in LEN. cbn [length] in LEN. lia. }
      eapply (rw_cells_transport bsegs) in FR; [| exact MU4| exact WM4| cbn; lia].
      eapply (rw_cells_transport bsegs) in ERR; [| exact MU4| exact WM4| cbn; lia].
      eapply (bytes_at_transport bsegs) in BY3; [| exact MU4| cbn; lia].
      assert (HL4 : ART AI sp0 SPB ((C, size) :: LBX) [] TRSX BX m4 mo g).
      { eapply (art_frame AI); [exact HL3| exact MU4| exact WM4|].
        constructor; [| constructor; [| constructor]].
        - do 7 right. left. exists C, size. cbn. split; [left; reflexivity| lia].
        - right; left. cbn. lia. }
      pose proof (cj_chain_frame _ _ m4 _ _ _ _ CH3 MU4 WM4 ltac:(intros A' n' Hin; cbn; pose proof (BSEP A' n' Hin); pose proof (BLO A' n' Hin); unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; lia)) as CH4.
      assert (PR4 : dpres sp0 LB [] (bv_unsigned sp) m0 m4).
      { eapply dpres_munch; [exact PR3| exact MU4| exact WM4| unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| try rewrite alloc_ceiling_eq; lia| intros A' n' Hin; pose proof (LSEP A' n' Hin); lia| try rewrite alloc_ceiling_eq; lia| lia| lia| exact LBLO| sclr_tac2]. }
      assert (SSZ4 : sh_zero m4 alloc_ceiling (2^47)).
      { eapply sh_zero_stack_munch; [exact SSZ3| exact MU4|]. constructor; [| constructor; [| constructor]]; cbn [fst snd]; sclr_tac2. }
      clear MU4 WM4 MI3 CH3 PR3 HL3 BLK3 SSZ3 ST3.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 0x544bc) with (wz AFREE) by reflexivity.
      apply evt_done. cbv beta.
      assert (HBF : cost_free <= BX) by (rewrite cost_free_eq in *; lia).
      eapply lscps_bind.
      { eapply (art_free_ok AI) with (lo := lo) (A := C) (n := size) (tl := []); rewrite ?unsigned_lit by lia;
          first [ exact HL4 | left; reflexivity | exact ST4 | exact ERR | exact MI4 | exact TP | reflexivity | exact HBF
                | split; [lia| unfold PC0_FREE; lia]
                | apply uwt_hook_nonfp; lia
                | eapply (tinv_room TI); [exact TV| exact st_free2]
                | alia ]. }
      cbv beta. intros ms5 mo5 g5 PO5.
      (nelim PO5 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 TRS5 -> MI5 ST5 ERR5 PR5 GM5 TP5 HL5)
.
      rewrite ?unsigned_lit in ST5, PR5, TP5 by lia. cbn [cb_remove] in PR5, HL5. rewrite Z.eqb_refl in PR5, HL5.
      replace (ret_pc (Z_to_bv 64 0x82568)) with (Z_to_bv 64 0x82568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply fuzz_delete; [| exact HP| | exact Hd|].
      - split; [exact HL5|]. split; [exact ST5|]. split. { eapply cj_pres_rw_cells; [exact PR5| exact FR| left; cbn; lia]. }
        split; [exists e; exact ERR5|]. split; [exact MI5|]. split.
        { eapply dpres_trans; [exact PR4|]. apply dpres_of_cj_pres. eapply cj_pres_weaken; [exact PR5| lia| | intros f Hf; exact Hf].
          intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact Hb. }
        split; [exact FRM|]. split; [exact FA|]. split; [eapply gmono_trans; [exact GM| exact GM5]|].
        split; [eapply (tinv_put TI); [exact TV| exact st_free2| exact TP5]|]. split; [exact NP|]. split.
        { eapply sh_zero_stack_pres; [apply dpres_of_cj_pres; exact PR5| exact SSZ4]. }
        right. split; [exact DR|]. split; [exact DIN|]. split; [|exact LEN].
        eapply cj_pres_bytes_at; [exact PR5| exact BY3|]. do 3 right; left. exists D, size. split; [exact DINX| lia].
      - eapply cj_chain_pres; [exact CH4| exact PR5|]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb.
      - rewrite cost_free_eq in *. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_min : forall LBX TRSX BX npX mm mo g fj Fv fcv (r : Z) (d : nat) (B : list cblock) (b0 : byte) (pre str rest : list byte)
        rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      linv LBX TRSX BX npX mm mo g fj Fv fcv -> Permutation (B ++ LB) LBX -> cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      B0 - FUZZ_COST size + cost_free + cost_malloc size + cost_free * Z.of_nat (length B) <= BX ->
      LSCPS bsegs POST (LST 0x8252c Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 (bv_unsigned b0)) x20 x21 x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros LI HP CH Hd SZ4 DEQ LPRE NONUL HB.
      (nelimp LI 13%nat; intros HL ST FR [e ERR] MI PR FRM FA GM TV NP SSZ DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. pose proof SPtop as SPT. pose proof SPhi as SPH.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
      pose proof (cost_malloc_pos size ltac:(lia)) as CMP.
      assert (HBM : cost_malloc size <= BX) by (rewrite cost_free_eq in *; lia).
      unfold AERRNO, ATP in ERR.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. cbv beta. eapply fuzz_delete; [exact LI| exact HP| exact CH| exact Hd| rewrite cost_free_eq in *; lia].
      - zstep. zstep.
        replace (Z_to_bv 64 0x544c0) with (wz AMALLOC) by reflexivity.
        apply evt_done. cbv beta.
        eapply lscps_bind.
        { eapply (art_malloc_ok AI) with (lo := lo) (n := size) (tl := []); rewrite ?unsigned_lit by lia;
            first [ exact HL | exact ST | exact ERR | exact MI | exact TP | reflexivity | exact HBM
                  | split; [lia| unfold PC0_MALLOC; lia]
                  | apply uwt_hook_nonfp; lia
                  | eapply (tinv_room TI); [exact TV| exact st_malloc]
                  | alia | lia ]. }
        cbv beta. intros ms2 mo2 g2 PO.
        (nelim PO 26%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 e2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 RES)
.
        rewrite ?unsigned_lit in ST2, PR2, TP2 by lia.
        replace (ret_pc (Z_to_bv 64 0x8253c)) with (Z_to_bv 64 0x8253c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (TV2 : TINV TI npX TRS2) by (eapply (tinv_put_or TI); [exact TV| exact st_malloc| exact TP2]).
        assert (LI2 : forall LBY BY mo' g', ART AI sp0 SPB LBY [] TRS2 BY m2 mo' g' -> gmono g g' -> linv LBY TRS2 BY npX m2 mo' g' fj Fv fcv).
        { intros LBY BY mo' g' HLY GMY. eapply linv_xfer; [exact LI| exact PR2| | exact HLY| exact ST2| exact ERR2| exact MI2| exact GMY| exact TV2| exact NP| exact FRM| intros; reflexivity].
          intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. right. exact Hb. }
        assert (CH2 : cj_chain CJ_PRINTABLE m2 d r B).
        { eapply cj_chain_pres; [exact CH| exact PR2|]. intros b Hb. eapply Permutation_in; [exact HP|]. apply in_or_app. left. exact Hb. }
        destruct RES as [[-> HL2]|(C & junk & -> & CR & CN & _ & HL2 & BLK & _)].
        + (* [comment removed for export] *)
          eapply lscps_step_evt. cbv beta delta [mkR].
          unfold wz. zstep. if_cases K'; zify_cond K'; [| exfalso; apply K'; reflexivity].
          apply evt_done. cbv beta.
          eapply fuzz_ret with (LX := B); [apply LI2; [exact HL2| exact GM2]| | rewrite cost_free_eq in *; lia].
          eapply Permutation_trans; [apply Permutation_sym; exact HP| apply Permutation_app_comm].
        + (nelimp CR 4%nat; intros C1 C2 C3 C4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
          eapply lscps_step_evt. cbv beta delta [mkR].
          unfold wz. zstep. if_cases K'; zify_cond K'; [exfalso; lia|].
          apply evt_done. cbv beta.
          eapply fuzz_copy; [apply LI2; [exact HL2| exact GM2]| exact HP| exact CH2| exact Hd| exact BLK| exact CN| lia| exact DEQ| exact LPRE| exact NONUL| rewrite cost_free_eq in *; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_printed : forall LB2 TRSX BX npX mm mo g fj Fv fcv (r : Z) (d : nat) (B : list cblock) (b0 : byte) (pre str rest : list byte) (rp : word)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      linv LB2 TRSX BX npX mm mo g fj Fv fcv ->
      ((rp = wz 0 /\ Permutation (B ++ LB) LB2) \/ (exists q k, rp = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LB) LB2)) ->
      cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      B0 - FUZZ_COST size + 2 * cost_free + cost_malloc size + cost_free * Z.of_nat (length B) <= BX ->
      LSCPS bsegs POST (LST 0x82524 Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) rp x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 (bv_unsigned b0)) x20 x21 x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros LI RES CH Hd SZ4 DEQ LPRE NONUL HB.
      (nelimp LI 13%nat; intros HL ST FR [e ERR] MI PR FRM FA GM TV NP SSZ DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. pose proof SPtop as SPT. pose proof SPhi as SPH. unfold AERRNO, ATP in ERR.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      pose proof (cost_malloc_pos size ltac:(lia)) as CMP.
      assert (HBF : cost_free <= BX) by (rewrite cost_free_eq in *; lia).
      eapply lscps_step_evt. cbv beta delta [mkR].
      destruct RES as [[-> HP2]|(q & k & -> & QNZ & HP2)].
      - unfold wz. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
        apply evt_done. cbv beta.
        eapply fuzz_min; [exact LI| exact HP2| exact CH| exact Hd| exact SZ4| exact DEQ| exact LPRE| exact NONUL| rewrite cost_free_eq in *; lia].
      - (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP2)) 4%nat; intros Q1 Q2 Q3 Q4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in Q1. bandM. sepM. try rewrite alloc_ceiling_eq in Q4.
        unfold wz. zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
        zstep.
        replace (Z_to_bv 64 0x544bc) with (wz AFREE) by reflexivity.
        apply evt_done. cbv beta.
        eapply lscps_bind.
        { eapply (art_free_ok AI) with (lo := lo) (A := q) (n := k) (tl := []); rewrite ?unsigned_lit by lia;
            first [ exact HL | eapply perm_in_head; exact HP2 | exact ST | exact ERR | exact MI | exact TP | reflexivity | exact HBF
                  | split; [lia| unfold PC0_FREE; lia]
                  | apply uwt_hook_nonfp; lia
                  | eapply (tinv_room TI); [exact TV| exact st_free1]
                  | alia ]. }
        cbv beta. intros ms2 mo2 g2 PO.
        (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 TRS2 -> MI2 ST2 ERR2 PR2 GM2 TP2 HL2)
.
        rewrite ?unsigned_lit in ST2, PR2, TP2 by lia.
        pose proof (perm_cb_remove _ _ _ _ HP2 (proj1 (art_nodup AI _ _ _ _ _ _ _ _ _ HL))) as HP3.
        replace (ret_pc (Z_to_bv 64 0x8252c)) with (Z_to_bv 64 0x8252c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        assert (INB : forall b, In b (B ++ LB) -> In b (cb_remove q LB2)). { intros b Hb. eapply Permutation_in; [exact HP3| exact Hb]. }
        eapply fuzz_min; [| exact HP3| | exact Hd| exact SZ4| exact DEQ| exact LPRE| exact NONUL|].
        + eapply linv_xfer; [exact LI| exact PR2| intros b Hb; apply INB; apply in_or_app; right; exact Hb| exact HL2| exact ST2| exact ERR2| exact MI2| exact GM2
                            | eapply (tinv_put TI); [exact TV| exact st_free1| exact TP2]| exact NP| exact FRM| intros; reflexivity].
        + eapply cj_chain_pres; [exact CH| exact PR2|]. intros b Hb. apply INB. apply in_or_app. left. exact Hb.
        + rewrite cost_free_eq in *. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_print_ret : forall (pc : Z) LB2 TRSX BX npX mm mo g fj Fv fcv (r : Z) (d : nat) (B : list cblock) (b0 : byte) (pre str rest : list byte) (rp : word)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
      (pc = 0x82508 \/ pc = 0x82518 \/ pc = 0x82524) ->
      linv LB2 TRSX BX npX mm mo g fj Fv fcv ->
      ((rp = wz 0 /\ Permutation (B ++ LB) LB2) \/ (exists q k, rp = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LB) LB2)) ->
      cj_chain CJ_PRINTABLE mm d r B -> (d <= 1001)%nat ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      B0 - FUZZ_COST size + 2 * cost_free + cost_malloc size + cost_free * Z.of_nat (length B) <= BX ->
      LSCPS bsegs POST (LST pc Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) rp x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 r) (Z_to_bv 64 (bv_unsigned b0)) x20 x21 x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros HPC LI RES CH Hd SZ4 DEQ LPRE NONUL HB.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      destruct HPC as [-> |[-> | ->]].
      1,2: eapply lscps_step_evt; cbv beta delta [mkR]; zstep; apply evt_done; cbv beta.
      all: eapply fuzz_printed; [exact LI| exact RES| exact CH| exact Hd| exact SZ4| exact DEQ| exact LPRE| exact NONUL| exact HB].
    Qed.

    (* [comment removed for export] *)
    Ltac after_print LI NP HP1 Hd SZ4 DEQ LPRE NONUL NPX LENB HB retpc :=
      cbv beta; intros ms3 mo3 g3 PO;
      (nelim PO 37%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 fc3 m3 e3 LB3 TRS3 B3 np3 -> MI3 FRM3 FA3 ST3 ERR3 PR3 CH3 HL3 TV3 NP3 GM3 HB3 RES3)
;
      rewrite ?unsigned_lit in ST3, PR3 by lia;
      replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [lia| reflexivity]);
      eapply (fuzz_print_ret retpc);
      [ lia
      | eapply linv_xfer; [exact LI| exact PR3| intros b Hb; apply in_or_app; right; exact Hb| exact HL3| exact ST3| exact ERR3| exact MI3| exact GM3| exact TV3
                          | revert NP NP3 NPX; clear; intros; unfold FUZZ_NP, PRINT_NP in *; lia | exact FRM3| exact FA3]
      | exact RES3 | exact CH3 | exact Hd | exact SZ4 | exact DEQ | exact LPRE | exact NONUL
      | revert HB3 HB LENB; clear; intros; rewrite cost_free_eq in *; lia ].

    (* [comment removed for export] *)
    Lemma fuzz_parsed : forall LB1 TRSX BX npX mm mo g fj Fv fcv (r blen : Z) (b0 b2 b3 : byte) (pre str rest : list byte)
        rav x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
      linv LB1 TRSX BX npX mm mo g fj Fv fcv ->
      ((r = 0 /\ Permutation LB1 LB)
       \/ (r <> 0 /\ exists (B : list cblock) (d : nat) (ch ty : Z) (p1 : word) (vs : Z) (vi p2 vd : word),
             cj_chain CJ_PRINTABLE mm d r B /\ (d <= 1001)%nat /\ Permutation LB1 (B ++ LB)
             /\ Z.of_nat (length B) <= blen + 1
             /\ rw_cells bsegs mm r (node_cells 0 (wz 0) ch ty p1 vs vi p2 vd 0))) ->
      4 < size -> data = pre ++ str ++ wb 0 :: rest -> length pre = 4%nat -> ~ In (wb 0) str ->
      npX + PRINT_NP <= np0 + FUZZ_NP size -> 0 <= blen ->
      B0 - FUZZ_COST size + PRINT_COST + 2 * cost_free + cost_malloc size + cost_free * (blen + 1) <= BX ->
      LSCPS bsegs POST (LST 0x824e4 Fv fcv mm rav x5 x6 x7 (Z_to_bv 64 size) (Z_to_bv 64 D) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 (bv_unsigned b2)) (Z_to_bv 64 (bv_unsigned b3)) x28 x29 x30 x31) mo g.
    Proof.
      intros until x31. intros LI RES SZ4 DEQ LPRE NONUL NPX BL0 HB.
      (nelimp LI 13%nat; intros HL ST FR [e ERR] MI PR FRM FA GM TV NP SSZ DAT).
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. pose proof SPtop as SPT. pose proof SPhi as SPH. unfold AERRNO, ATP in ERR.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      pose proof (cost_malloc_pos size ltac:(lia)) as CMP.
      pose proof (bv_unsigned_in_range 8 b2) as Rb2. change (bv_modulus 8) with 256 in Rb2.
      pose proof (bv_unsigned_in_range 8 b3) as Rb3. change (bv_modulus 8) with 256 in Rb3.
      eapply lscps_step_evt. cbv beta delta [mkR].
      destruct RES as [[-> HP1]|(RNZ & B & d & ch & ty & p1 & vs & vi & p2 & vd & CH & Hd & HP1 & LENB & ND)].
      - zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
        apply evt_done. cbv beta.
        eapply fuzz_ret with (LX := []); [exact LI| rewrite app_nil_r; exact HP1| unfold PRINT_COST in HB; rewrite cost_free_eq in *; lia].
      - (nelimp (cj_chain_ptr_range _ _ _ _ _ CH) 3%nat; intros R1 R2 R3).
        apply Permutation_sym in HP1.
        assert (HPR : PRINT_COST <= BX) by (rewrite cost_free_eq in *; lia).
        assert (HNP : npX + PRINT_NP <= NPMAX TI) by lia.
        assert (LFR : lf_room 1 [] (Z.of_nat d)) by (unfold lf_room; cbn [lf_count]; change (fcap 1) with 8192; lia).
        zstep. if_cases K; zify_cond K; [exfalso; exact (RNZ K)|]. clear K.
        zstep. zstep. zstep. if_cases K1; zify_cond K1.
        + (* [comment removed for export] *)
          zstep. if_cases K2; zify_cond K2.
          * (* [comment removed for export] *)
            zstep. zstep.
            apply evt_done. cbv beta. eapply lscps_bind.
            { pose proof PRU as X. unfold cjprintu_stmt, print_pre_stmt, CJPRINTU_ENTRY, wz in X.
              eapply X with (lo := lo) (LR := LB) (B := B) (n := d); clear X; rewrite ?E1; rewrite ?unsigned_lit by lia;
                first [ exact HL | exact HP1 | exact CH | exact RNZ | exact Hd | exact SPB2 | exact AL | exact SP0 | exact ST | exact CEIL | exact BOT | exact ERR | exact MI
                      | exact TP | exact FRM | exact SSZ | exact TV | exact HNP | exact st_print | exact LFR | exact HPR | reflexivity | exact I
                      | unfold is_pc0, PC0_MALLOC, PC0_FREE, PC0_REALLOC; lia | alia ]. }
            after_print LI NP HP1 Hd SZ4 DEQ LPRE NONUL NPX LENB HB 0x82524.
          * (* [comment removed for export] *)
            zstep. zstep.
            apply evt_done. cbv beta. eapply lscps_bind.
            { pose proof PRF as X. unfold cjprint_stmt, print_pre_stmt, CJPRINT_ENTRY, wz in X.
              eapply X with (lo := lo) (LR := LB) (B := B) (n := d); clear X; rewrite ?E1; rewrite ?unsigned_lit by lia;
                first [ exact HL | exact HP1 | exact CH | exact RNZ | exact Hd | exact SPB2 | exact AL | exact SP0 | exact ST | exact CEIL | exact BOT | exact ERR | exact MI
                      | exact TP | exact FRM | exact SSZ | exact TV | exact HNP | exact st_print | exact LFR | exact HPR | reflexivity | exact I
                      | unfold is_pc0, PC0_MALLOC, PC0_FREE, PC0_REALLOC; lia | alia ]. }
            after_print LI NP HP1 Hd SZ4 DEQ LPRE NONUL NPX LENB HB 0x82518.
        + (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep.
          apply evt_done. cbv beta. eapply lscps_bind.
          { pose proof PRB as X. unfold pbuffered_stmt, print_pre_stmt, PBUFD_ENTRY, wz in X.
            eapply X with (lo := lo) (LR := LB) (B := B) (n := d); clear X; rewrite ?E1; rewrite ?unsigned_lit by lia;
              first [ exact HL | exact HP1 | exact CH | exact RNZ | exact Hd | exact SPB2 | exact AL | exact SP0 | exact ST | exact CEIL | exact BOT | exact ERR | exact MI
                    | exact TP | exact FRM | exact SSZ | exact TV | exact HNP | exact st_print | exact LFR | exact HPR | reflexivity | exact I
                    | exists 1; split; [reflexivity| lia]
                    | unfold is_pc0, PC0_MALLOC, PC0_FREE, PC0_REALLOC; lia | alia ]. }
          after_print LI NP HP1 Hd SZ4 DEQ LPRE NONUL NPX LENB HB 0x82508.
    Qed.

    (* [comment removed for export] *)
    Lemma fuzz_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mo : Model) (errv : word),
      ART AI sp0 SPB LB [] TRS0 B0 m0 mo g0 -> TINV TI np0 TRS0 ->
      (size <= 4 \/ (In (D, size) LB /\ bytes_at bsegs m0 D data /\ Z.of_nat (length data) = size)) ->
      rw_cells bsegs m0 AERRNO [C4 errv] -> mem_inv bsegs m0 ->
      stk bsegs m0 lo (bv_unsigned sp) -> frm0 fc -> sh_zero m0 alloc_ceiling (2^47) ->
      LSCPS bsegs POST
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x82384) fc None m0 (seg_rom bsegs)) mo g0.
    Proof.
      intros until errv. intros HL TV PAY ERR MI ST FRM SSZ.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK in LO'.
      pose proof SPFeq as E1. pose proof SPFal as AL. pose proof SPtop as SPT. pose proof SPhi as SPH.
      (nelimp (art_binv AI _ _ _ _ _ _ _ _ _ HL) 4%nat; intros _ _ BXR _).
      pose proof (art_shbase AI _ _ _ _ _ _ _ _ _ HL) as SB. shbase_split SB.
      unfold AERRNO, ATP in ERR. pose proof (conj ERR I) as ERRbox. clear ERR.
      pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
      assert (BLO : forall A n, In (A, n) LB -> AIMG_HI <= A /\ A + n <= alloc_ceiling).
      { intros A n Hin. (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL Hin) 4%nat; intros ? _ ? ?). lia. }
      eapply lscps_step_evt. cbv beta delta [mkR].
      carve_frame 64%nat ST.
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      do 8 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : ART AI sp0 SPB LB [] TRS0 B0 m1 mo g0).
      { eapply (art_frame_store AI); [exact HL| exact MU| exact WM| alia| lia]. }
      assert (ERR1 : rw_cells bsegs m1 AERRNO [C4 errv]).
      { eapply errno_high_store; [exact (proj1 ERRbox)| exact MU| exact WM| alia]. }
      assert (PR1 : dpres sp0 LB [] (bv_unsigned sp) m0 m1).
      { apply dpres_of_cj_pres. eapply (cj_pres_stack_store AI); [exact HL| intros b Hb; exact Hb| exact MU| exact WM| alia| lia]. }
      assert (SSZ1 : sh_zero m1 alloc_ceiling (2^47)).
      { eapply sh_zero_stack_munch; [exact SSZ| exact MU|]. constructor; [| constructor]. cbn [fst snd]. sclr_tac2. }
      zstep. zstep. zstep. if_cases K0; zify_cond K0.
      - (* [comment removed for export] *)
        apply evt_done. cbv beta.
        eapply (fuzz_ret LB [] TRS0 B0 np0); [| rewrite app_nil_r; apply Permutation_refl| unfold FUZZ_COST, PRINT_COST; lia].
        split; [exact HL1|]. split; [exact ST|]. split; [exact FR|]. split; [exists errv; exact ERR1|]. split; [exact MI|].
        split; [exact PR1|]. split; [exact FRM|]. split; [intros; reflexivity|]. split; [apply gmono_refl|]. split; [exact TV|].
        split; [unfold FUZZ_NP; lia|]. split; [exact SSZ1| left; lia].
      - destruct PAY as [?|(DIN & BY & LEN)]; [exfalso; lia|].
        pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL DIN) as DR. (nelimp DR 4%nat; intros D1 D2 D3 D4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in D1. bandM. sepM. try rewrite alloc_ceiling_eq in D4.
        eapply (bytes_at_transport bsegs) in BY; [| exact MU| cbn; lia].
        clear MU WM.
        pose proof (art_block_shadow_ok AI _ _ _ _ _ _ _ _ _ _ _ HL1 DIN) as SO.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        replace (size + D + -1) with (D + size - 1) by lia.
        ugd. zstep. zstep. zstep.
        replace (Z.lxor (Z.b2z (0 <? D)) (Z.b2z (D + size - 1 <? 1))) with 1
          by (rewrite (proj2 (Z.ltb_lt 0 D) ltac:(lia)); rewrite (proj2 (Z.ltb_ge (D + size - 1) 1) ltac:(lia)); reflexivity).
        ugd. ugd.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep.
        pose proof (shadow_ok_shchk1 m1 D size (D + size - 1) SO ltac:(lia)) as CKl. asan_chk CKl.
        destruct (nth_error data (Z.to_nat (size - 1))) as [bl|] eqn:Hbl. 2:{ exfalso. apply nth_error_None in Hbl. lia. }
        pose proof (u8ro_read bsegs m1 D data (size - 1) bl _ BY Hbl ltac:(lia) eq_refl) as RDl.
        pose proof (bv_unsigned_in_range 8 bl) as Rbl. change (bv_modulus 8) with 256 in Rbl.
        (* [comment removed for export] *)
        assert (RET : forall rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31,
                  LSCPS bsegs POST (LST 0x82570 F fc m1 rav x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31) mo g0).
        { intros. eapply (fuzz_ret LB [] TRS0 B0 np0); [| rewrite app_nil_r; apply Permutation_refl| unfold FUZZ_COST, PRINT_COST; lia].
          split; [exact HL1|]. split; [exact ST|]. split; [exact FR|]. split; [exists errv; exact ERR1|]. split; [exact MI|].
          split; [exact PR1|]. split; [exact FRM|]. split; [intros; reflexivity|]. split; [apply gmono_refl|]. split; [exact TV|].
          split; [unfold FUZZ_NP; lia|]. split; [exact SSZ1|]. right. split; [exact DR|]. split; [exact DIN|]. split; [exact BY| exact LEN]. }
        replace (D + size - 1) with (D + (size - 1)) by lia.
        zstep. cbv beta. zstep. if_cases K1; zify_cond K1; [apply evt_done; cbv beta; apply RET|].
        (* [comment removed for export] *)
        destruct (nth_error data 0) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
        destruct (nth_error data 1) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
        destruct (nth_error data 2) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. lia. }
        destruct (nth_error data 3) as [b3|] eqn:Hb3. 2:{ exfalso. apply nth_error_None in Hb3. lia. }
        pose proof (u8ro_read bsegs m1 D data 0 b0 _ BY Hb0 ltac:(lia) eq_refl) as RD0.
        pose proof (u8ro_read bsegs m1 D data 1 b1 _ BY Hb1 ltac:(lia) eq_refl) as RD1.
        pose proof (u8ro_read bsegs m1 D data 2 b2 _ BY Hb2 ltac:(lia) eq_refl) as RD2.
        pose proof (u8ro_read bsegs m1 D data 3 b3 _ BY Hb3 ltac:(lia) eq_refl) as RD3.
        pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
        pose proof (bv_unsigned_in_range 8 b1) as Rb1. change (bv_modulus 8) with 256 in Rb1.
        pose proof (bv_unsigned_in_range 8 b2) as Rb2. change (bv_modulus 8) with 256 in Rb2.
        pose proof (bv_unsigned_in_range 8 b3) as Rb3. change (bv_modulus 8) with 256 in Rb3.
        replace (wa (D + 0)) with (wa D) in RD0 by (f_equal; lia).
        (* [comment removed for export] *)
        zstep. zstep.
        pose proof (shadow_ok_shchk1 m1 D size D SO ltac:(lia)) as CK0. asan_chk CK0.
        zstep. cbv beta. zstep. zstep. zstep. if_cases K2; zify_cond K2; [apply evt_done; cbv beta; apply RET|].
        zstep. ugd.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shchk1 m1 D size (D + 1) SO ltac:(lia)) as CK1'. asan_chk CK1'.
        zstep. cbv beta. zstep. zstep. zstep. if_cases K3; zify_cond K3; [apply evt_done; cbv beta; apply RET|].
        zstep. ugd.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shchk1 m1 D size (D + 2) SO ltac:(lia)) as CK2'. asan_chk CK2'.
        zstep. cbv beta.
        assert (J2 : forall z10 z13 z14, evt bsegs (fun ms' => LSCPS bsegs POST ms' mo g0)
                  (LST 0x8247c F fc m1 ra t0 t1 t2 (Z_to_bv 64 size) (Z_to_bv 64 D) z10 (Z_to_bv 64 2147450880) (Z_to_bv 64 (bv_unsigned b1)) z13 z14 a5 a6 a7
                       s2 (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 (bv_unsigned b2)) s5 t3 t4 t5 t6)).
        2:{ zstep. zstep. if_cases Kb2; zify_cond Kb2; [apply J2|].
            zstep. ugd. zstep. zstep. if_cases K4; zify_cond K4; [apply evt_done; cbv beta; apply RET| apply J2]. }
        intros z10 z13 z14. zstep. ugd.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        pose proof (shadow_ok_shchk1 m1 D size (D + 3) SO ltac:(lia)) as CK3'. asan_chk CK3'.
        zstep. cbv beta.
        assert (J3 : forall z10 z11 z13 z14, evt bsegs (fun ms' => LSCPS bsegs POST ms' mo g0)
                  (LST 0x824c8 F fc m1 ra t0 t1 t2 (Z_to_bv 64 size) (Z_to_bv 64 D) z10 z11 (Z_to_bv 64 (bv_unsigned b1)) z13 z14 a5 a6 a7
                       s2 (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 (bv_unsigned b2)) (Z_to_bv 64 (bv_unsigned b3)) t3 t4 t5 t6)).
        2:{ zstep. zstep. if_cases Kb3; zify_cond Kb3.
            - zstep. ugd. zstep. zstep. if_cases K5; zify_cond K5; [apply evt_done; cbv beta; apply RET|]. zstep. ugd. apply J3.
            - zstep. zstep. if_cases Kw; zify_cond Kw; [apply J3|]. exfalso. lia. }
        clear z10 z13 z14. intros z10 z11 z13 z14. zstep. ugd.
        zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        destruct (split4 data ltac:(lia)) as [DEQ4 LPRE].
        assert (Ebl : bl = wb 0) by (apply bv_eq; rewrite K1; reflexivity).
        assert (INZ : In (wb 0) (skipn 4 data)).
        { rewrite <- Ebl. eapply (nth_error_In _ (Z.to_nat (size - 1) - 4)). rewrite nth_error_skipn, <- Hbl. f_equal. lia. }
        (nelim (nul_split _ INZ) 4%nat; intros str rest EQT NONUL).
        assert (DEQ : data = firstn 4 data ++ str ++ wb 0 :: rest) by (rewrite <- EQT; exact DEQ4).
        assert (SL : 4 + Z.of_nat (length str) + 1 + Z.of_nat (length rest) = size).
        { rewrite DEQ, !length_app, LPRE in LEN. cbn [length] in LEN. lia. }
        assert (BYV : bytes_at bsegs m1 (D + 4) (str ++ [wb 0])).
        { pose proof BY as B2. rewrite DEQ in B2. apply bytes_at_app in B2. destruct B2 as [_ B2]. rewrite LPRE in B2.
          replace (str ++ wb 0 :: rest) with ((str ++ [wb 0]) ++ rest) in B2 by (rewrite <- app_assoc; reflexivity).
          apply bytes_at_app in B2. destruct B2 as [B2 _]. exact B2. }
        (* [comment removed for export] *)
        apply evt_done. cbv beta.
        assert (PRE : parse_doc_pre AI TI (Z_to_bv 64 SPF) (Z_to_bv 64 size) (Z_to_bv 64 0x824e4) tp fc m1 mo g0 sp0 SPB LB TRS0 np0 B0 D size lo
                        (Z.of_nat (length str) + 1) errv).
        { unfold parse_doc_pre. rewrite E1, !unsigned_lit by lia.
          split; [exact HL1|]. split; [exact TV|]. split; [exact DIN|]. split; [exact ERR1|]. split; [exact MI|].
          split; [exact ST|]. split; [exact CEIL|]. split; [exact BOT|]. split; [alia|].
          split; [lia|]. split; [lia|]. split; [exact SPB2|]. split; [lia|]. split; [exact SP0|].
          split; [exact AL|]. split; [lia|]. split; [lia|]. split; [unfold is_pc0, PC0_MALLOC, PC0_FREE, PC0_REALLOC; lia|].
          split; [exact FRM|]. split; [exact TP|].
          split; [exact st_pwlo_head|]. split; [exact st_pv_pwlo|]. split; [exact st_pv_pobj|]. split; [exact st_parse_const_delete|].
          revert HB0 SL SZ; clear; intros; unfold FUZZ_COST, PRINT_COST, pdoc_cost, pv_cost_pre, PV_FRATE, PV_RATE in *; rewrite cost_free_eq in *; lia. }
        eapply lscps_bind.
        { pose proof PARSE as X. unfold parse_wopts_stmt, PARSE_WOPTS, wz in X.
          eapply X with (D := D) (n := size) (str := str) (V := D + 4); clear X;
            first [ exact PRE | exact BYV | exact NONUL | reflexivity | lia ]. }
        cbv beta. intros ms2 mo2 g2 PO.
        (nelim PO 37%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 r LB' TRS' B' e2 -> A0 FAG FRM2 MI2 ST2 ERR2 HL2 TV2 GM2 HB2 BYT DP RES)
.
        unfold wz in A0. subst a0'. rewrite ?E1 in ST2, DP.
        replace (ret_pc (Z_to_bv 64 0x824e4)) with (Z_to_bv 64 0x824e4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply (fuzz_parsed LB' TRS' B' np0) with (pre := firstn 4 data) (str := str) (rest := rest) (blen := Z.of_nat (length str) + 1);
          [| exact RES| lia| exact DEQ| exact LPRE| exact NONUL| unfold FUZZ_NP, PRINT_NP; lia| lia
           | pose proof (fuzz_budget size (Z.of_nat (length str) + 1) ltac:(lia) ltac:(lia)); lia].
        split; [exact HL2|]. split; [exact ST2|]. split.
        { eapply dpres_rw_cells_stack; [exact DP| exact FR| lia| cbn; lia| alia]. }
        split; [exists e2; exact ERR2|]. split; [exact MI2|]. split.
        { eapply dpres_trans; [exact PR1|]. eapply dpres_weaken; [exact DP| lia| intros b Hb; exact Hb]. }
        split; [exact FRM2|]. split.
        { intros k Hk. apply FAG; unfold fp_callee_saved in Hk; lia. }
        split; [exact GM2|]. split; [exact TV2|]. split; [unfold FUZZ_NP; lia|]. split.
        { eapply sh_zero_stack_pres; [exact DP| exact SSZ1]. }
        right. split; [exact DR|]. split; [exact DIN|]. split; [| exact LEN].
        eapply dpres_bytes_at_block; [exact DR| exact DIN| exact DP| exact BY| lia].
    Qed.
  End Body.

  Theorem llvmfuzz_spec_gen : llvmfuzz_stmt AI TI S_LIB.
  Proof.
    unfold llvmfuzz_stmt. intros until errv. intros HL TV NPM STATL PAY SZ ERR MI ST CEIL LO SPB1 SPAL SPB2 SP0 TOP BOT SPS0 FRM TP A0 A1 HB SSZ.
    unfold AFUZZ_ENTRY, wz. unfold wz in A0, A1. subst a0 a1.
    eapply fuzz_entry; [exact STATL| exact SPB1| exact SPB2| exact SPAL| exact SP0| exact TOP| exact SPS0| exact CEIL| exact BOT| exact LO| exact TP| exact SZ| exact NPM
                      | exact HB| exact HL| exact TV| exact PAY| exact ERR| exact MI| exact ST| exact FRM| exact SSZ].
  Qed.
End S.

(* [comment removed for export] *)
Theorem llvmfuzz_spec : forall AI TI,
  parse_wopts_stmt AI TI -> pbuffered_stmt AI TI -> cjprint_stmt AI TI -> cjprintu_stmt AI TI ->
  llvmfuzz_stmt AI TI S_LIB.
Proof.
  intros AI TI PA PB PF PU.
  eapply llvmfuzz_spec_gen; [exact PA| exact PB| exact PF| exact PU| exact ICPT_mem2.asan_memcpy_ok| intros tr H; exact H].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac alia := first [ unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in *; rewrite ?alloc_ceiling_eq in *; unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK, DELETE_STACK, APRINT_STACK, APV_STACK, AMALLOC_STACK, AINTRIN_STACK, MINIFY_STACK in *; lia | sclr_tac2 ].
Ltac ugd := let G := fresh "G" in zstep; if_cases G; zify_cond G; try (exfalso; lia).
