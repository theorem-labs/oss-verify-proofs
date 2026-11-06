(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr FP ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_utraps CJ_ensure CJ_pstr_B CJ_pv_common CJ_pv_ctx CJ_pv_update CJ_pv_cases.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Local Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Local Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Local Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS ?R ?F ?pc _ _ ?m _) => idtac "PC" pc "MEM" m "F" F "REGS" R;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.

Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr usegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma disjoint_from_forall : forall (W : list (Z * Z)) A k,
  (forall iv, In iv W -> A + k <= fst iv \/ snd iv <= A) -> disjoint_from W A k.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros A k HW; cbn; [exact I|]. split.
  - exact (HW (lo1, hi1) ltac:(left; reflexivity)).
  - apply IH. intros iv Hiv. apply HW. right; exact Hiv.
Qed.

Lemma outside_forall : forall (W : list (Z * Z)) a,
  (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros a HW; cbn; [exact I|]. split.
  - exact (HW (lo1, hi1) ltac:(left; reflexivity)).
  - apply IH. intros iv Hiv. apply HW. right; exact Hiv.
Qed.

Lemma Forall_forall_W : forall (P : Z * Z -> Prop) (W : list (Z * Z)),
  (forall iv, In iv W -> P iv) -> Forall P W.
Proof. intros P W H. apply Forall_forall. exact H. Qed.

Ltac killK K := first [exfalso; lia | exfalso; apply K; reflexivity].
Notation M1 := 18446744073709551615.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).
  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis TP : tp = wz PTP.
  Hypothesis SPhi : bv_unsigned sp <= 2^64.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis BLR : forall b, In b B -> In b LR.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis DEP0 : 0 <= dep.
  Hypothesis PNZ : p <> 0.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.

  Notation POST := (pvalue_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m).
  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells usegs mm (bv_unsigned sp + -128)
     [CB 40 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells usegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 91236); C8 (Z_to_bv 64 90916); C8 (Z_to_bv 64 97488)]).
  Notation ACTX := (actx HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 F m SPB LR PB fw lo).

  (* [comment removed for export] *)
  Definition PTST (mm : word -> option byte) (t : word) : Prop := rw_cells usegs mm (bv_unsigned sp + -128) [C8 t].
  Definition PTXT (mm : word -> option byte) (tx : list byte) : Prop := rw_cells usegs mm (bv_unsigned sp + -120) [CB 32 tx].
  Definition PFH (mm : word -> option byte) : Prop :=
    rw_cells usegs mm (bv_unsigned sp + -88)
      [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition NCTX (depc : Z) (mm : word -> option byte) (mo : Model) (errv : word)
      (LB : list cblock) (buf len off : Z) (bs : list byte) : Prop :=
    LHEAP HI SPB LB mm mo /\ Permutation ((buf, len) :: LR) LB /\ PBSd mm buf len off depc /\ u8arr usegs mm buf bs /\ Z.of_nat (length bs) = len
    /\ pb_nums len off depc /\ stk usegs mm lo SPF /\ rw_cells usegs mm PERRNO [C4 errv] /\ mem_inv usegs mm /\ CJST mm
    /\ pv_agree LR (bv_unsigned sp) PB m mm.

  Lemma pieces_join : forall mm t tx,
    PTST mm t -> PTXT mm tx -> PFH mm -> PVFRAME mm (le8 t ++ tx).
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm t tx H1 H2 H3.
    assert (LTX : length tx = 32%nat) by (destruct H2 as [[W _] _]; cbn in W; destruct W as [W _]; exact W).
    unfold PTST, PTXT, PFH in *.
    assert (H2' : rw_cells usegs mm (bv_unsigned sp + -128 + Z.of_nat (cells_size [C8 t])) [CB 32 tx]).
    { replace (bv_unsigned sp + -128 + Z.of_nat (cells_size [C8 t])) with (bv_unsigned sp + -120) by (cbn [cells_size csize Nat.add]; lia). exact H2. }
    pose proof (proj2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app _ _ _ _ _) (conj H1 H2')) as J2.
    assert (H3' : rw_cells usegs mm (bv_unsigned sp + -128 + Z.of_nat (cells_size ([C8 t] ++ [CB 32 tx])))
                    [C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { replace (bv_unsigned sp + -128 + Z.of_nat (cells_size ([C8 t] ++ [CB 32 tx]))) with (bv_unsigned sp + -88) by (cbn [cells_size csize Nat.add app]; lia). exact H3. }
    pose proof (proj2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app _ _ _ _ _) (conj J2 H3')) as J3.
    cbn [app] in J3.
    change (C8 t :: CB 32 tx :: ?rest) with ([] ++ [C8 t; CB 32 tx] ++ rest) in J3.
    pose proof (rw_cells_merge _ _ _ [] [C8 t; CB 32 tx] _ J3) as J.
    cbn [cells_size csize cells_bytes cbytes Nat.add app] in J. rewrite app_nil_r in J.
    exact J.
  Qed.

  Lemma pieces_split : forall mm t tx,
    PVFRAME mm (le8 t ++ tx) -> length tx = 32%nat ->
    PTST mm t /\ PTXT mm tx /\ PFH mm.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm t tx FR LTX.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 32]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in FR by (rewrite length_le8; lia).
    rewrite skipn_app, length_le8, Nat.sub_diag, skipn_O, skipn_all2 in FR by (rewrite length_le8; lia). cbn [app] in FR.
    rewrite firstn_all2 in FR by lia.
    apply (proj1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app _ _ _ [CB 8 (le8 t)] _)) in FR. destruct FR as [H1 FR].
    apply (proj1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.rw_cells_app _ _ _ [CB 32 tx] _)) in FR. destruct FR as [H2 H3].
    cbn [cells_size csize Nat.add] in H2, H3.
    replace (bv_unsigned sp + -128 + Z.of_nat 8) with (bv_unsigned sp + -120) in H2 by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 32) with (bv_unsigned sp + -88) in H3 by lia.
    split; [| split; [exact H2| exact H3]].
    unfold PTST. destruct H1 as [[Hwf HB] HW]. split; [split; [cbn; split; exact I| exact HB]| exact HW].
  Qed.

  Lemma nctx_actx : forall depc mm mo Fc fcc errv LB buf len off bs loc,
    NCTX depc mm mo errv LB buf len off bs -> PVFRAME mm loc -> frm0 fcc -> FAG18 F Fc -> ACTX depc mm mo loc Fc fcc errv LB buf len off bs.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until loc. intros (HL & HP & PBS0 & ARR & LEN & PN & ST & ERR & MI & CJ & PVA) FR FRM FA.
    split; [exact HL|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact PN|].
    split; [exact FR|]. split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact CJ|]. split; [exact FRM|]. split; [exact FA| exact PVA].
  Qed.

  Lemma actx_nctx : forall depc mm mo Fc fcc errv LB buf len off bs loc,
    ACTX depc mm mo loc Fc fcc errv LB buf len off bs -> NCTX depc mm mo errv LB buf len off bs /\ PVFRAME mm loc /\ frm0 fcc /\ FAG18 F Fc.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until loc. intros nelH_; (nelim nelH_ 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    split; [| split; [exact FR| split; [exact FRM| exact FA]]].
    split; [exact HL|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact PN|].
    split; [exact ST|]. split; [exact ERR|]. split; [exact MI|]. split; [exact CJ| exact PVA].
  Qed.

  (* [comment removed for export] *)
  Lemma nctx_call : forall depc mm mm' mo errv errv' LB buf len off bs (W : list (Z * Z)),
    NCTX depc mm mo errv LB buf len off bs ->
    munch W mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' -> stk usegs mm' lo SPF ->
    rw_cells usegs mm' PERRNO [C4 errv'] ->
    (forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SPF + 40) \/ iv = (PERRNO, PERRNO + 4)) ->
    NCTX depc mm' mo errv' LB buf len off bs.
  Proof using PL CEIL LO. clear TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until W. intros (HL & HP & PBS0 & ARR & LEN & PN & ST & ERR & MI & CJ & PVA) MU WM MI' ST' ERR' HW.
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    assert (DJ : forall A k, (A + k <= lo \/ SPF + 40 <= A) -> (A + k <= PERRNO \/ PERRNO + 4 <= A) -> disjoint_from W A k).
    { intros A k H1 H2. apply disjoint_from_forall. intros iv Hiv. destruct (HW iv Hiv) as [[X1 X2]| ->]; cbn [fst snd] in *; lia. }
    unfold PERRNO in DJ.
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. apply Forall_forall_W. intros [lo1 hi1] Hiv.
             destruct (HW _ Hiv) as [[X1 X2]|E]; [| inversion E; subst]; cbn [fst snd] in *.
             - right; left. cbn [fst snd]. try rewrite alloc_ceiling_eq. lia.
             - right; right; left. cbn [fst snd]. lia. }
    split; [exact HP|].
    split. { eapply rw_cells_transport; [exact PBS0| exact MU| exact WM|]. apply DJ; cbn; lia. }
    split. { eapply u8arr_transport; [exact ARR| exact MU| exact WM|]. apply DJ; lia. }
    split; [exact LEN|]. split; [exact PN|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { destruct CJ as (CJa & (ge1 & ge2 & CJb) & CJc).
             split; [| split; [exists ge1, ge2|]];
               (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DJ; unfold PHOOKS, PGERROR, PLCONV; cbn [cells_size csize Nat.add]; lia]). }
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
    intros a Ha [Hc Hn]. apply outside_forall. intros iv Hiv. destruct (HW iv Hiv) as [[X1 X2]| ->]; cbn [fst snd]; unfold PERRNO.
    - destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ Q _).
      try rewrite alloc_ceiling_eq in Q. lia.
    - destruct Hc as [Hs|[[Hd Hns]|(A' & n' & Hin & Hr)]]; [lia| | ].
      + intros X. apply Hns. unfold palloc_static, PERRNO. lia.
      + (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ Q Q5).
        try rewrite alloc_ceiling_eq in Q. unfold PIMG_LO, PIMG_HI in Q5. lia.
  Qed.

  Ltac open_actx CTX :=
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA);
    pose proof CEIL as CEIL'; unfold PV_STACK, PV_BASE in LO; try rewrite alloc_ceiling_eq in CEIL;
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4); pose proof PN as PNc; (nelim PN 3%nat; intros PN1 PN2 PN3); unfold PERRNO in ERR;
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5);
    try rewrite alloc_ceiling_eq in R4; unfold PIMG_LO, PIMG_HI in R5.
  Ltac tree_now CTX CHn := assert (CHn : cj_chain CJ_PRINTABLE _ n p B) by (eapply (actx_tree HI); [exact PL| exact CEIL| exact LO| exact BLR| exact CTX| exact CH0]).

  (* [comment removed for export] *)
  Lemma num_T : forall mm mo loc Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    ACTX dep mm mo loc Fc fcc errv LB buf len off bs -> 0 <= r -> off + r + 2 <= len ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off + r)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x149a0) fcc None mm (seg_rom usegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX R0 ROOM. tree_now CTX CHn. open_actx CTX.
    pose proof (munch_refl [(buf + off, buf + len); (PB, PB + 64)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. rewrite (unsigned_lit PB), (align8_land7 PB PL4) by lia.
    ustore_at buf off (buf + off + r) r (wb 0) ltac:(reflexivity).
    step. if_false.
    step. zstep. step. step.
    apply evt_done. cbv beta.
    eapply pv_ret1; [exact CEIL'| unfold PV_STACK, PV_BASE; lia| exact N1| exact FR| exact ST| exact MI| exact ERR| | exact FRM| exact FA| | | | exact HP| exact PBS0| | |].
    - eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[E1|[]]]; inversion E1; subst; unfold PDATA_LO, PIMG_HI; lia.
    - eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
      intros a Ha [Hc Hn]. cbn [outside]. split; [|split; [lia| exact I]].
      destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
      destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
    - eapply cj_chain_frame; [exact CHn| exact MU| exact WM|].
      intros A' n' Hin. destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' (BLR _ Hin)) as [_ D].
      (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ Q _).
      try rewrite alloc_ceiling_eq in Q. cbn. lia.
    - eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor; [|constructor]].
      + do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia].
      + right; left. cbn. lia.
    - split; [exact ARR| rewrite !upd_length; exact LEN].
    - split; [lia| split; [exact PN2| exact DEP0]].
    - exists 0. split; [lia|]. split; [lia|]. replace (off + r + 0) with (off + r) by lia. apply nth_error_upd_same. rewrite ?upd_length. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tx_read : forall mm (tx : list byte) (i : Z),
    bytes_at usegs mm (bv_unsigned sp + -120) tx -> length tx = 32%nat -> 0 <= i < 32 ->
    exists b : byte, ov_read_bytes usegs mm (wa (bv_unsigned sp + -120 + i)) 1 = Some [b].
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm tx i TX LTX Hi.
    destruct (nth_error tx (Z.to_nat i)) as [b|] eqn:E.
    - exists b. eapply u8ro_read; [exact TX| exact E| lia| reflexivity].
    - exfalso. apply nth_error_None in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma num_loop : forall (r : Z) (tx : list byte) (m0 : word -> option byte) (buf off len : Z) (Fc : bvmap 5 word) (fcc : bv 32) (a4 : word)
      x1 x5 x6 x7 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31 (k : nat) (i : Z) mm (bsi : list byte) x15 x16,
    (Z.to_nat (r - i) <= k)%nat -> 0 <= i < r -> r <= 32 -> length tx = 32%nat ->
    0 <= off -> off + r + 2 <= len -> cblock_range buf len -> 64 < bv_unsigned a4 ->
    u8arr usegs mm buf bsi -> Z.of_nat (length bsi) = len -> bytes_at usegs mm (bv_unsigned sp + -120) tx -> mem_inv usegs mm ->
    munch [(buf + off, buf + off + r)] m0 mm -> wmono usegs m0 mm ->
    evt usegs (fun ms' => exists mm' bs' x11' x15' x16',
        ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off + r)) x11' (Z_to_bv 64 (M1 - (buf + off))) (Z_to_bv 64 (bv_unsigned sp + -120)) a4 x15' x16' x17
                     x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                Fc (Z_to_bv 64 0x149a0) fcc None mm' (seg_rom usegs)
        /\ u8arr usegs mm' buf bs' /\ Z.of_nat (length bs') = len /\ bytes_at usegs mm' (bv_unsigned sp + -120) tx /\ mem_inv usegs mm'
        /\ munch [(buf + off, buf + off + r)] m0 mm' /\ wmono usegs m0 mm')
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 i) (Z_to_bv 64 (M1 - (buf + off))) (Z_to_bv 64 (bv_unsigned sp + -120)) a4 x15 x16 x17
               x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x1497c) fcc None mm (seg_rom usegs)).
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until a4. intros x1 x5 x6 x7 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31.
    induction k as [|k IH]; intros i mm bsi x15 x16 Hk Hi Hr LTX OFF ROOM CR A4 ARR LEN TX MI MU WM; [exfalso; lia|].
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelim CR 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    (* [comment removed for export] *)
    assert (STORE : forall v : Z, 0 <= v < 256 ->
      evt usegs (fun ms' => exists mm' bs' x11' x15' x16',
        ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off + r)) x11' (Z_to_bv 64 (M1 - (buf + off))) (Z_to_bv 64 (bv_unsigned sp + -120)) a4 x15' x16' x17
                     x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
                Fc (Z_to_bv 64 0x149a0) fcc None mm' (seg_rom usegs)
        /\ u8arr usegs mm' buf bs' /\ Z.of_nat (length bs') = len /\ bytes_at usegs mm' (bv_unsigned sp + -120) tx /\ mem_inv usegs mm'
        /\ munch [(buf + off, buf + off + r)] m0 mm' /\ wmono usegs m0 mm')
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 i) (Z_to_bv 64 (M1 - (buf + off))) (Z_to_bv 64 (bv_unsigned sp + -120)) a4 (Z_to_bv 64 v) x16 x17
               x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x1496c) fcc None mm (seg_rom usegs))).
    { intros v Hv.
      zstep. zstep.
      ustore_at buf off (buf + off + i) i (wb v) ltac:(symmetry; apply le1_lit8; lia).
      step. if_cases Ke; zify_cond Ke.
      - (* [comment removed for export] *)
        step. if_cases Kg; zify_cond Kg; first [killK Kg | idtac]. clear Kg. zstep.
        apply evt_done. nexists 5%nat. split; [reflexivity|].
        split; [exact ARR|]. split; [rewrite upd_length; exact LEN|]. split; [exact TX|]. split; [exact MI|]. split; [exact MU| exact WM].
      - eapply (IH (i + 1)); [lia| lia| exact Hr| exact LTX| exact OFF| exact ROOM| | exact A4| exact ARR| rewrite upd_length; exact LEN| exact TX| exact MI| exact MU| exact WM].
        split; [lia|]. split; [exact R2|]. split; [lia|]. split; [try rewrite alloc_ceiling_eq; lia| unfold PIMG_LO, PIMG_HI; lia]. }
    destruct (tx_read mm tx i TX LTX ltac:(lia)) as [b RD].
    pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
    step. if_cases Kg; zify_cond Kg; first [killK Kg | idtac]. clear Kg.
    step. if_cases Kg; zify_cond Kg; first [killK Kg | idtac]. clear Kg.
    zstep. step. step. if_cases Kd; zify_cond Kd.
    - apply STORE. lia.
    - step. step. apply STORE. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma actx_block_write : forall depc mm mm' mo loc Fc fcc errv LB buf len off bs bs' (a b : Z),
    ACTX depc mm mo loc Fc fcc errv LB buf len off bs ->
    munch [(a, b)] mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
    u8arr usegs mm' buf bs' -> Z.of_nat (length bs') = len -> buf <= a -> b <= buf + len ->
    ACTX depc mm' mo loc Fc fcc errv LB buf len off bs'.
  Proof using PL CEIL LO. clear TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until b. intros CTX MU WM MI' ARR' LEN' A0 Bl.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4).
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor].
             do 4 right. exists buf, len. split; [eapply perm_in_head; exact HP| cbn; lia]. }
    split; [exact HP|].
    split. { eapply rw_cells_transport; [exact PBS0| exact MU| exact WM|]. cbn. lia. }
    split; [exact ARR'|]. split; [exact LEN'|]. split; [exact PN|].
    split. { eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia. }
    split. { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn. lia. }
    split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. unfold PERRNO. cbn. lia. }
    split; [exact MI'|].
    split. { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E1|[]]; inversion E1; subst; unfold PDATA_LO, PIMG_HI; lia. }
    split; [exact FRM|]. split; [exact FA|].
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM|].
    intros x Hx [Hc Hn]. cbn [outside]. split; [| exact I].
    destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
    destruct (lheap_perm_apart HI _ _ _ _ _ _ _ HL HP A' n' Hin) as [_ D]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_tx : forall mm t tx,
    PVFRAME mm (le8 t ++ tx) -> length tx = 32%nat -> bytes_at usegs mm (bv_unsigned sp + -120) tx.
  Proof. clear PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros mm t tx FR LTX. (nelim (pieces_split mm t tx FR LTX) 3%nat; intros _ H2 _).
    destruct H2 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. exact BY.
  Qed.

  (* [comment removed for export] *)
  Lemma num_J : forall mm mo t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    ACTX dep mm mo (le8 t ++ tx) Fc fcc errv LB buf len off bs -> length tx = 32%nat ->
    0 <= r <= 25 -> off + r + 2 <= len ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) (Z_to_bv 64 (buf + off)) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x14954) fcc None mm (seg_rom usegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX LTX Hr ROOM. pose proof CTX as (HL & HP & _ & ARR & LEN & (PN1 & PN2 & PN3) & FR & _ & _ & MI & _).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4).
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as CR. (nelimp CR 5%nat; intros R1 R2 R3 R4 R5). try rewrite alloc_ceiling_eq in R4. unfold PIMG_LO, PIMG_HI in R5.
    pose proof (frame_tx mm t tx FR LTX) as TX.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. if_cases K0; zify_cond K0.
    - apply evt_done. cbv beta. subst r. replace (buf + off) with (buf + off + 0) by lia. eapply num_T; [exact CTX| lia| lia].
    - step. zstep. rewrite zb_lxor_ones by lia. zstep. zstep. step.
      eapply evt_cut.
      { eapply (num_loop r tx mm buf off len Fc fcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat r) 0 mm bs);
          first [exact LTX| exact ROOM| exact CR| exact ARR| exact LEN| exact TX| exact MI| apply munch_refl| apply wmono_refl| lia
                | rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with 18446744073709551616;
                  rewrite <- (Z.mod_add _ 1 18446744073709551616) by lia; rewrite Z.mod_small by lia; lia]. }
      cbv beta. intros ms' nelH_; (nelim nelH_ 12%nat; intros mm' bs' x11' x15' x16' -> ARR' LEN' TX' MI' MU' WM').
      apply evt_done. eapply num_T; [eapply actx_block_write; [exact CTX| exact MU'| exact WM'| exact MI'| exact ARR'| exact LEN'| lia| lia]| lia| lia].
  Qed.

  Ltac open_fctx FC := (nelim FC 9%nat; intros FR ST ERR MI CJ FRM FA PVA CHn); unfold PERRNO in ERR.

  (* [comment removed for export] *)
  Lemma num_E : forall mm mo t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    ACTX dep mm mo (le8 t ++ tx) Fc fcc errv LB buf len off bs -> length tx = 32%nat ->
    0 <= r <= 25 ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x14944) fcc None mm (seg_rom usegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX LTX Hr. pose proof CTX as (HL & _).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. pose proof LO as LO'. unfold PV_STACK, PV_BASE in LO'.
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    zstep. step. step. apply evt_done. cbv beta.
    eapply scps_bind. { eapply (actx_ensure HI); [exact PL| exact CEIL| exact LO| exact BLR| exact TP| exact N1| exact CH0| exact CTX| lia]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 buf2 len2 -> HL2 FC2 PBS2 OUT).
    replace (ret_pc (Z_to_bv 64 0x14950)) with (Z_to_bv 64 0x14950) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
    destruct OUT as [(-> & HB) | (bs2 & -> & CTX2 & ROOM)].
    - step. if_cases K; zify_cond K; first [killK K | idtac]. clear K. apply evt_done. cbv beta.
      open_fctx FC2.
      eapply pv_epi; [exact CEIL| exact LO| exact N1| exact FR| exact ST| exact MI| exact ERR| exact CJ| exact FRM| exact FA| exact PVA| exact CHn|].
      exists LB2, buf2, len2, off. split; [exact HL2|]. left. split; [reflexivity|]. exists dep. split; [exact PBS2| exact HB].
    - (nelimp (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ (proj1 (proj2 CTX2)))) 5%nat; intros Y1 _ _ Y4 _). try rewrite alloc_ceiling_eq in Y4.
      (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). pose proof CTX2 as (_ & _ & _ & _ & _ & (PN1 & PN2 & PN3) & _).
      step. if_cases K; zify_cond K; first [killK K | idtac]. clear K. apply evt_done. cbv beta.
      eapply num_J; [exact CTX2| exact LTX| exact Hr| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma num_L : forall mm mo t tx Fc fcc errv LB buf len off bs (r : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    ACTX dep mm mo (le8 t ++ tx) Fc fcc errv LB buf len off bs -> length tx = 32%nat ->
    0 <= r <= 25 ->
    SCPS usegs POST
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 (Z_to_bv 64 PB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 46) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          Fc (Z_to_bv 64 0x14934) fcc None mm (seg_rom usegs)) mo.
  Proof using PL CEIL LO TP SPhi N1 BLR SPAL DEP0 PNZ CH0.
    intros until x31. intros CTX LTX Hr. pose proof CTX as (HL & _).
    eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
    step. step. if_cases K; zify_cond K; first [idtac | killK K].
    all: try (apply evt_done; cbv beta; eapply num_E; [exact CTX| exact LTX| exact Hr]).
    all: killK K.
  Qed.
End S.


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac shh H := let T := type of H in idtac H ":" T.
Ltac shmem :=
  lazymatch goal with |- evt _ _ (MS ?R ?F ?pc _ _ ?m _) => idtac "PC" pc "MEM" m "F" F "REGS" R;
    repeat match goal with H : context [m] |- _ => shh H; revert H end end.
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr usegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
Ltac killK K := first [exfalso; lia | exfalso; apply K; reflexivity].
Notation M1 := 18446744073709551615.
