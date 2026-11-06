(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit IcptKit2 F_gates M_sspdefs M_stdio_base I_memset_i N_ictx N_stkhi N_rfile N_intscan_lib N_vfscanf_lib N_vfscanf_E.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition A0_scanf_common : Z := 0x47c60.
Definition A0_vfscanf_i : Z := 0x44144.
Definition A0_FMT : Z := 0x218e0.
Definition A0_FMT2 : Z := 0x21ac0.
Definition SC_DEPTH : Z := 2400.

Definition sc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q.

Definition scanf_common_gen (FA FN W3num : Z) : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (AP P1 P2 P3 r lo : Z) (w3 : word),
  mem_inv asegs m -> icpt_env m -> stk asegs m lo q -> 0x10007fff8000 <= lo -> lo <= q - SC_DEPTH -> q < 2^64 -> q mod 16 = 0 ->
  1 <= r <= W3num ->
  rw_cells asegs m AP [C8 (wz P1); C8 (wz P2); C8 w3] -> (W3num = 3 -> w3 = wz P3) -> q <= AP -> AP + 24 < 2^64 ->
  accessible m FA FN -> sh_readable m FA FN ->
  accessible m P1 4 -> sh_readable m P1 4 -> cwin P1 4 -> P1 + 4 < 2^47 ->
  accessible m P2 4 -> sh_readable m P2 4 -> cwin P2 4 -> P2 + 4 < 2^47 ->
  accessible m P3 4 -> sh_readable m P3 4 -> cwin P3 4 -> P3 + 4 < 2^47 ->
  evt asegs (sc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 (wz r) (wz FA) (wz AP) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_scanf_common) fc None m (seg_rom asegs)).
Definition scanf_common_stmt : Prop := scanf_common_gen A0_FMT 11 3.
Definition scanf_common2_stmt : Prop := scanf_common_gen A0_FMT2 8 2.

Lemma vfs_range : forall fuel fmt f mt r, 0 <= mt -> vfs fuel fmt f mt = Some r -> r = -1 \/ mt <= r <= mt + nconv fmt.
Proof.
  induction fmt as [|d fmt IH]; intros f mt r Hm H; cbn [vfs nconv] in *.
  - injection H as <-. lia.
  - pose proof (nconv_nonneg fmt) as NN.
    destruct d; cbn [nconv]; (lazymatch type of H with match ?X with _ => _ end = _ => destruct X eqn:E end;
      [ apply IH in H; [lia|lia] | injection H as <-; destruct (mt =? 0) eqn:E0; [left; reflexivity| right; apply Z.eqb_neq in E0; lia] | injection H as <-; lia | discriminate H ]).
Qed.
Lemma model_range : forall fmtd txt p r, sscanf_model fmtd txt p = Some r -> r = -1 \/ 0 <= r <= nconv fmtd.
Proof. intros fmtd txt p r H. unfold sscanf_model in H. apply vfs_range in H; [|lia]. lia. Qed.

Lemma fmt_at : forall m, mem_inv asegs m -> bytes_at asegs m A0_FMT (zbytes FMTL_STATUS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A0_FMT; lia| unfold A0_FMT; rewrite zbytes_length; cbn [length FMTL_STATUS]; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma fmt2_at : forall m, mem_inv asegs m -> bytes_at asegs m A0_FMT2 (zbytes FMTL_VERSION).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A0_FMT2; lia| unfold A0_FMT2; rewrite zbytes_length; cbn [length FMTL_VERSION]; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Definition pctx (FA FN P1 P2 P3 : Z) (m : mem) : Prop :=
  (accessible m FA FN /\ sh_readable m FA FN)
  /\ (accessible m P1 4 /\ sh_readable m P1 4) /\ (accessible m P2 4 /\ sh_readable m P2 4) /\ (accessible m P3 4 /\ sh_readable m P3 4).
Lemma pctx_frame : forall FA FN P1 P2 P3 W m m', pctx FA FN P1 P2 P3 m -> munch W m m' -> shw_ok W -> cwin FA FN -> cwin P1 4 -> cwin P2 4 -> cwin P3 4 -> pctx FA FN P1 P2 P3 m'.
Proof.
  intros FA FN P1 P2 P3 W m m' ((AF & RF) & (A1 & R1) & (A2 & R2) & (A3 & R3)) MU OK CF C1 C2 C3.
  pose proof (shw_outside W) as HO.
  repeat split;
    first [ eapply accessible_munch; [eassumption| exact MU| eassumption| intros s Hs; apply HO; [exact OK| lia]]
          | eapply sh_readable_munch; [eassumption| exact MU| eassumption| intros s Hs; apply HO; [exact OK| lia]] ].
Qed.

Definition psep (T L P1 P2 P3 : Z) : Prop :=
  (P1 + 4 <= T \/ T + L <= P1) /\ (P2 + 4 <= T \/ T + L <= P2) /\ (P3 + 4 <= T \/ T + L <= P3)
  /\ (P1 + 4 <= P2 \/ P2 + 4 <= P1) /\ (P1 + 4 <= P3 \/ P3 + 4 <= P1) /\ (P2 + 4 <= P3 \/ P3 + 4 <= P2).
Section SS.
  Variables (T p : Z) (txt pre post : list Z) (canary : word) (P1 P2 P3 lox qx : Z) (tp : word).

  Variables (FA FN : Z) (fmtl : list Z) (fmtd ds' : list sdir) (W3num : Z) (w3n : nat) (a4w : word).
  Hypothesis SC : scanf_common_gen FA FN W3num.
  Hypothesis FMD : fmtd = SD :: ds'.
  Hypothesis FMB : forall m, mem_inv asegs m -> bytes_at asegs m FA (zbytes fmtl).
  Hypothesis HFA : 0x10000 <= FA /\ FA + zlength fmtl <= 0x32000.
  Hypothesis FMR : Forall (fun c => 0 <= c < 256) fmtl.
  Hypothesis FE : fmt_enc fmtl fmtd.
  Hypothesis HNC : nconv fmtd <= W3num.
  Hypothesis HW3 : (W3num = 2 /\ w3n = 0%nat) \/ (W3num = 3 /\ w3n = 4%nat).
  Hypothesis HAP3 : W3num = 3 -> a4w = wz P3.
  Hypothesis FNW : cwin FA FN.
  Hypothesis TXT : rtext T txt pre post.
  Hypothesis Hp : p = zlength pre.
  Hypothesis T0 : 0x609000 <= T.
  Hypothesis TLO : T + zlength txt <= lox.
  Hypothesis HP1 : 0x609000 <= P1 /\ P1 + 4 <= lox.
  Hypothesis HP2 : 0x609000 <= P2 /\ P2 + 4 <= lox.
  Hypothesis HP3 : 0x609000 <= P3 /\ P3 + 4 <= lox.
  Hypothesis PSEP : psep T (zlength txt) P1 P2 P3.
  Hypothesis HP1w : cwin P1 4.
  Hypothesis HP2w : cwin P2 4.
  Hypothesis HP3w : cwin P3 4.
  Hypothesis IW : iwin T p lox qx tp.
  Hypothesis TPV : bv_unsigned tp = 6190512.
  Ltac shw_P H := cbn [fst snd]; let X := fresh "CW" in pose proof H as X; unfold cwin in X; lia.

  Ltac shw_ss := unfold shw_ok;
    apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_cons; [cbn [fst snd]; lia|];
    apply Forall_cons; [shw_P HP1w|]; apply Forall_cons; [shw_P HP2w|]; apply Forall_cons; [shw_P HP3w|];
    apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_nil.

  Definition vfu_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte) (ev v1 v2 v3 : word),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (vf_FP q P1 P2 P3) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (q - VF_DEPTH) q
      /\ rw_cells asegs m' (q + 56) [CB 232 junk]
      /\ bytes_at asegs m' T (zbytes txt) /\ ssp_cells m' canary
      /\ rw_cells asegs m' ERRNOA [C4 ev]
      /\ rw_cells asegs m' (q + 400) [C8 (wz P1); C8 (wz P2); C8 a4w]
      /\ rw_cells asegs m' P1 [C4 v1] /\ rw_cells asegs m' P2 [C4 v2] /\ rw_cells asegs m' P3 [C4 v3].

  #[using="pre post fmtl ds' W3num w3n FMD FMB HFA FMR FE HNC HW3 HAP3 TXT Hp T0 TLO HP1 HP2 HP3 PSEP HP1w HP2w HP3w IW TPV"] Lemma vfscanf_uni : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ev v1 v2 v3 : word) (r : Z),
    stk asegs m (q - VF_DEPTH) q -> mem_inv asegs m ->
    rw_cells asegs m (q + 56) (ss_cells T 0 0 w0 T 0 w0 w0) ->
    rw_cells asegs m (q + 400) [C8 (wz P1); C8 (wz P2); C8 a4w] ->
    rw_cells asegs m P1 [C4 v1] -> rw_cells asegs m P2 [C4 v2] -> rw_cells asegs m P3 [C4 v3] ->
    bytes_at asegs m T (zbytes txt) -> ssp_cells m canary -> rw_cells asegs m ERRNOA [C4 ev] ->
    sscanf_model fmtd txt p = Some r ->
    ictx T p lox qx m -> lox <= q - VF_DEPTH -> q + 448 <= qx ->
    evt asegs (vfu_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (q + 56)) (wz FA) (wz (q + 400)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz VFSCANF) fc None m (seg_rom asegs)).
  Proof.
    intros until r. intros ST MI FC APC PC1 PC2 PC3 BY SSP ERR HV IC LOX QXQ.
    pose proof IW as IW'. destruct IW' as (CWT & W2T & NST & KLOX & LQX & QX47 & TPLO & TPHI).
    pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40). unfold zlength in *.
    pose proof (zbytes_length txt) as LTX. subst fmtd.

    Ltac lva_prem := first
      [ exact TXT | exact Hp | reflexivity | exact TPV | exact IW | exact FMR | exact HW3 | exact HAP3 | exact FE | exact HNC | eassumption
      | exact (proj1 PSEP) | exact (proj1 (proj2 PSEP)) | exact (proj1 (proj2 (proj2 PSEP)))
      | exact (proj1 (proj2 (proj2 (proj2 PSEP)))) | exact (proj1 (proj2 (proj2 (proj2 (proj2 PSEP))))) | exact (proj2 (proj2 (proj2 (proj2 (proj2 PSEP)))))
      | unfold cwinP; pose proof HP1w as X; unfold cwin in X; lia | unfold cwinP; pose proof HP2w as X; unfold cwin in X; lia | unfold cwinP; pose proof HP3w as X; unfold cwin in X; lia
      | apply FMB; assumption
      | unfold VF_DEPTH, zlength in *; lia | right; unfold zlength; lia | left; unfold VF_DEPTH, zlength; lia | intros _; left; unfold VF_DEPTH; lia ].
    destruct HW3 as [[E2 E0]|[E3 E4]].
    -
      assert (PH : rw_cells asegs m P3 [CB w3n []]).
      { subst w3n. unfold rw_cells, cells_at, bytes_at, wr_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize length app Z.of_nat Nat.add].
        repeat split; try reflexivity; try exact I; try lia; intros i Hi; exfalso; lia. }
      pose proof (stk_of_rw_cells asegs _ _ _ PC3) as S3. cbn [cells_size csize Nat.add] in S3.
      eapply evt_mono.
      { eapply N_vfscanf_E.L_VA with (q := q) (T := T) (p := p) (txt := txt) (pre := pre) (post := post) (canary := canary)
          (P1 := P1) (P2 := P2) (P3 := P3) (FA := FA) (fmtl := fmtl) (fuel := S (length txt)) (W3num := W3num) (w3n := w3n)
          (ap3w := a4w) (lox := lox) (qx := qx) (ds' := ds') (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := []);
          first [ exact PH | exact FC | exact APC | exact PC1 | exact PC2 | exact BY | exact SSP | exact ERR | exact HV | exact ST | exact MI | exact IC | lva_prem ]. }
      intros ms' PO. unfold vf_post in PO. unfold vfu_post.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & fjunk & ev' & w1 & w2 & w3
                      & E & MU' & WM' & MI' & ST' & FCj & BY' & SSP' & ERR' & APC' & PCa & PCb & _).
      pose proof (stk_hi_wmono m m' _ _ S3 WM' ltac:(lia)) as S3'.
      destruct (stk_carve asegs m' P3 (P3 + Z.of_nat 4) 4 S3' ltac:(lia)) as [_ [j4 PC3']].
      replace (P3 + Z.of_nat 4 - Z.of_nat 4) with P3 in PC3' by lia.
      apply (CellConv.rw_cells_CB_C4 asegs m' P3 [] j4 []) in PC3'. cbn [app] in PC3'.
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', fjunk, ev', w1, w2, (le_bytes_to_word j4).
      repeat (split; [assumption|]). exact PC3'.
    -
      destruct (rw_cells_forget _ _ _ _ PC3) as [b3 PC3']. cbn [cells_size csize Nat.add] in PC3'. rewrite <- E4 in PC3'.
      eapply evt_mono.
      { eapply N_vfscanf_E.L_VA with (q := q) (T := T) (p := p) (txt := txt) (pre := pre) (post := post) (canary := canary)
          (P1 := P1) (P2 := P2) (P3 := P3) (FA := FA) (fmtl := fmtl) (fuel := S (length txt)) (W3num := W3num) (w3n := w3n)
          (ap3w := a4w) (lox := lox) (qx := qx) (ds' := ds') (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := b3);
          first [ exact PC3' | exact FC | exact APC | exact PC1 | exact PC2 | exact BY | exact SSP | exact ERR | exact HV | exact ST | exact MI | exact IC | lva_prem ]. }
      intros ms' PO. unfold vf_post in PO. unfold vfu_post.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & fjunk & ev' & w1 & w2 & w3
                      & E & MU' & WM' & MI' & ST' & FCj & BY' & SSP' & ERR' & APC' & PCa & PCb & PCc).
      rewrite E4 in PCc. apply (CellConv.rw_cells_CB_C4 asegs m' P3 [] w3 []) in PCc. cbn [app] in PCc.
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', fjunk, ev', w1, w2, (le_bytes_to_word w3).
      repeat (split; [assumption|]). exact PCc.
  Qed.

  Definition vfi_W (q : Z) : list ivl :=
    [(q - 48 - VF_DEPTH, q); (q + 8, q + 8 + 232); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (ERRNOA, ERRNOA + 4)].
  Definition vfi_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte) (ev v1 v2 v3 : word),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (vfi_W q) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (q - 48 - VF_DEPTH) q
      /\ rw_cells asegs m' (q + 8) [CB 232 junk]
      /\ bytes_at asegs m' T (zbytes txt) /\ ssp_cells m' canary
      /\ rw_cells asegs m' ERRNOA [C4 ev]
      /\ rw_cells asegs m' (q + 352) [C8 (wz P1); C8 (wz P2); C8 a4w]
      /\ rw_cells asegs m' P1 [C4 v1] /\ rw_cells asegs m' P2 [C4 v2] /\ rw_cells asegs m' P3 [C4 v3].

  #[using="pre post fmtl ds' W3num w3n SC FMD FMB HFA FMR FE HNC HW3 HAP3 FNW TXT Hp T0 TLO HP1 HP2 HP3 PSEP HP1w HP2w HP3w IW TPV"] Lemma vfscanf_i_spec : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ev v1 v2 v3 : word) (r : Z),
    stk asegs m (q - 48 - VF_DEPTH) q -> mem_inv asegs m ->
    rw_cells asegs m (q + 8) (ss_cells T 0 0 w0 T 0 w0 w0) ->
    rw_cells asegs m (q + 352) [C8 (wz P1); C8 (wz P2); C8 a4w] ->
    rw_cells asegs m P1 [C4 v1] -> rw_cells asegs m P2 [C4 v2] -> rw_cells asegs m P3 [C4 v3] ->
    bytes_at asegs m T (zbytes txt) -> ssp_cells m canary -> rw_cells asegs m ERRNOA [C4 ev] ->
    sscanf_model fmtd txt p = Some r ->
    ictx T p lox qx m -> pctx FA FN P1 P2 P3 m ->
    lox <= q - 48 - VF_DEPTH -> q + 400 <= qx -> q mod 16 = 0 ->
    evt asegs (vfi_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (q + 8)) (wz FA) (wz (q + 352)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A0_vfscanf_i) fc None m (seg_rom asegs)).
  Proof.
    intros until r. intros ST MI FC APC PC1 PC2 PC3 BY SSP ERR HV IC PX LOX QXQ Q16.
    pose proof IW as IW'. destruct IW' as (CWT & W2T & NST & KLOX & LQX & QX47 & TPLO & TPHI).
    pose proof (munch_refl (vfi_W q) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold vfi_W, VF_DEPTH, ERRNOA in MU. unfold VF_DEPTH in ST, LOX. unfold ERRNOA in ERR. unfold A0_vfscanf_i.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40). unfold zlength in *.
    pose proof (zbytes_length txt) as LTX.
    zstep.
    carve_frame 48%nat ST.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IC1 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_ss]) end.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ (ictx_env _ _ _ _ _ IC1)) |].
    clear IC1.
    zstep. lit_branch.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IC1 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_ss]) end.
    pose proof (ie_real_lib _ (ictx_env _ _ _ _ _ IC1)) as (_ & RL2 & _).
    do 7 zstep.
    replace (q + 8) with (q + -48 + 56) in * by lia. replace (q + 352) with (q + -48 + 400) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (IC2 : ictx T p lox qx mm) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_ss]);
      eapply evt_cut;
      [ eapply vfscanf_uni with (q := (q + -48)%Z) (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := v3);
        [ eassumption | assumption | exact FC | exact APC | exact PC1 | exact PC2 | exact PC3 | exact BY | split; [exact SSP1| exact SSP2] | exact ERR
        | exact HV | exact IC2 | unfold VF_DEPTH; lia | lia ]
      | ] end.
    unfold vfu_post, vf_FP, VF_DEPTH, ERRNOA.
    clear IC1 IC2 RL2.
    lazymatch goal with |- forall ms', _ -> evt _ _ _ => lazymatch goal with MI1 : mem_inv asegs ?mm |- _ => post_call asegs mm end end.
    clear APC SSP1 SSP2.
    lazymatch goal with H : ssp_cells _ canary |- _ => destruct H as [SSP1 SSP2]; unfold got_ssp, ssp_guard in SSP1, SSP2 end.
    pose proof (model_range _ _ _ _ HV) as RR.
    zstep. zstep.
    assert (BL : bv_lts z64 (Z_to_bv 64 r) = (0 <? r)).
    { unfold bv_lts. pose proof (nconv_nonneg fmtd) as NN0. destruct HW3 as [[? _]|[? _]]; rewrite (SFModel.signed_of_Z r) by lia; reflexivity. }
    rewrite BL. clear BL.
    destruct (Z.ltb_spec 0 r) as [RP|RN]; cbn [negb].
    -
      do 6 zstep.
      replace (q + -48 + 400) with (q + 352) in * by lia.
      pose proof SC as SC'. unfold scanf_common_gen in SC'.
      lazymatch goal with MUc : munch _ m ?mm, WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (IC3 : ictx T p lox qx mm) by (eapply ictx_frame; [exact IC| exact IW| exact MUc| exact WMc| shw_ss]);
        assert (PX3 : pctx FA FN P1 P2 P3 mm) by (eapply pctx_frame; [exact PX| exact MUc| shw_ss| exact FNW| exact HP1w| exact HP2w| exact HP3w]);
        destruct PX3 as ((AF & RF) & (A1 & R1) & (A2 & R2) & (A3 & R3));
        eapply evt_cut;
        [ eapply SC' with (AP := (q + 352)%Z) (P1 := P1) (P2 := P2) (P3 := P3) (r := r) (lo := (q + -48 - 2960)%Z) (w3 := a4w);
          [ assumption | exact (ictx_env _ _ _ _ _ IC3) | eassumption | lia | unfold SC_DEPTH; lia | lia
          | clear - Q16; Z.div_mod_to_equations; lia | pose proof (nconv_nonneg fmtd); lia
          | eassumption | exact HAP3 | lia | lia
          | exact AF | exact RF
          | exact A1 | exact R1 | exact HP1w | lia | exact A2 | exact R2 | exact HP2w | lia | exact A3 | exact R3 | exact HP3w | lia ]
        | post_call asegs mm ] end.
      clear SC'.
      do 7 zstep.
      lazymatch goal with P : stk asegs _ _ (q + -48) |- _ => release_frame FR P q end.
      replace (q + -48 + 56) with (q + 8) in * by lia.
      unfold vfi_post, vfi_W, VF_DEPTH, ERRNOA, ssp_cells, got_ssp, ssp_guard.
      finish.
      all: eassumption.
    -
      do 7 zstep.
      lazymatch goal with P : stk asegs _ _ (q + -48) |- _ => release_frame FR P q end.
      replace (q + -48 + 56) with (q + 8) in * by lia. replace (q + -48 + 400) with (q + 352) in * by lia.
      unfold vfi_post, vfi_W, VF_DEPTH, ERRNOA, ssp_cells, got_ssp, ssp_guard.
      finish.
      all: eassumption.
  Qed.

  #[using="Type"] Lemma rw_cells_reshape : forall segs m A cs cs',
    rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells segs m A cs'.
  Proof. intros segs m A cs cs' [[W B] S] W' B' S'. split; [split; [exact W'| rewrite B'; exact B]| rewrite S'; exact S]. Qed.
  #[using="Type"] Lemma file_cells_zero : forall segs m A, rw_cells segs m A [CB 232 (repeat (Z_to_bv 8 0) 232)] ->
    rw_cells segs m A [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                         C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Proof.
    intros segs m A H. apply (rw_cells_reshape segs m A _ _ H); [cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
  Qed.

  Definition A0_vsscanf : Z := 0xa2450.
  Definition VS_DEPTH : Z := 3296.
  Definition vs_W (q : Z) : list ivl := [(q - VS_DEPTH, q); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (ERRNOA, ERRNOA + 4)].
  Definition vs_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev v1 v2 v3 : word),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (vs_W q) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (q - VS_DEPTH) q
      /\ bytes_at asegs m' T (zbytes txt) /\ ssp_cells m' canary
      /\ rw_cells asegs m' ERRNOA [C4 ev]
      /\ rw_cells asegs m' (q + 64) [C8 (wz P1); C8 (wz P2); C8 a4w]
      /\ rw_cells asegs m' P1 [C4 v1] /\ rw_cells asegs m' P2 [C4 v2] /\ rw_cells asegs m' P3 [C4 v3].

  #[using="pre post fmtl ds' W3num w3n SC FMD FMB HFA FMR FE HNC HW3 HAP3 FNW TXT Hp T0 TLO HP1 HP2 HP3 PSEP HP1w HP2w HP3w IW TPV"] Lemma vsscanf_spec : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ev v1 v2 v3 : word) (r : Z),
    stk asegs m (q - VS_DEPTH) q -> mem_inv asegs m ->
    rw_cells asegs m (q + 64) [C8 (wz P1); C8 (wz P2); C8 a4w] ->
    rw_cells asegs m P1 [C4 v1] -> rw_cells asegs m P2 [C4 v2] -> rw_cells asegs m P3 [C4 v3] ->
    bytes_at asegs m T (zbytes txt) -> ssp_cells m canary -> rw_cells asegs m ERRNOA [C4 ev] ->
    sscanf_model fmtd txt p = Some r ->
    ictx T p lox qx m -> pctx FA FN P1 P2 P3 m ->
    lox <= q - VS_DEPTH -> q + 112 <= qx -> q mod 16 = 0 ->
    evt asegs (vs_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz T) (wz FA) (wz (q + 64)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A0_vsscanf) fc None m (seg_rom asegs)).
  Proof.
    intros until r. intros ST MI APC PC1 PC2 PC3 BY SSP ERR HV IC PX LOX QXQ Q16.
    pose proof IW as IW'. destruct IW' as (CWT & W2T & NST & KLOX & LQX & QX47 & TPLO & TPHI).
    pose proof (munch_refl (vs_W q) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold vs_W, VS_DEPTH, ERRNOA in MU. unfold VS_DEPTH in ST, LOX. unfold ERRNOA in ERR. unfold A0_vsscanf.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40). unfold zlength in *.
    pose proof (zbytes_length txt) as LTX.
    carve_frame 48%nat ST. rename FR into FRV.
    carve_frame 232%nat ST. rename FR into FILE.
    destruct (stk_split _ _ _ (q + -288)%Z _ ST ltac:(lia)) as [ST8 STJ]. clear ST. rename ST8 into ST.
    do 16 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (IC1 : ictx T p lox qx mm) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| unfold shw_ok; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_cons; [shw_P HP1w|]; apply Forall_cons; [shw_P HP2w|]; apply Forall_cons; [shw_P HP3w|]; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_nil]);
      eapply evt_cut;
      [ eapply memset_i_spec with (P := (q + -280)%Z) (c := 0) (n := 232) (lo := (q + -3296)%Z);
        [ exact FILE
        | exact (proj1 (ictx_stack _ _ _ _ _ (q + -280) 232 IC1 ltac:(lia) ltac:(lia) ltac:(lia)))
        | exact (proj2 (ictx_stack _ _ _ _ _ (q + -280) 232 IC1 ltac:(lia) ltac:(lia) ltac:(lia)))
        | exact (ictx_env _ _ _ _ _ IC1)
        | exact (proj1 (iwin_stack _ _ _ _ _ (q + -280) 232 IW ltac:(lia) ltac:(lia) ltac:(lia)))
        | lia | lia | replace (q + -3296) with (q - 3296) by lia; exact ST | lia | lia | lia | right; lia | assumption | reflexivity | reflexivity | reflexivity | lia ]
      | post_call asegs mm ] end.
    clear IC1.
    lazymatch goal with H : rw_cells _ _ (q + -280) [CB (Z.to_nat 232) _] |- _ =>
      change (Z.to_nat 232) with 232%nat in H; apply file_cells_zero in H; rename H into FC end.
    do 3 zstep.
    zstep. fix_lit_store.
    zstep.
    zstep. fix_lit_store.
    zstep.
    replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 M64) in FC by (apply Z_to_bv_eqm; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FCv : rw_cells asegs mm (q + -288 + 8) (ss_cells T 0 0 w0 T 0 w0 w0))
        by (unfold ss_cells, w0, zero4, STRING_READ; replace (q + -288 + 8) with (q + -280) by lia; exact FC) end.
    clear FC.
    do 4 zstep.
    replace (q + -280) with (q + -288 + 8) in * by lia. replace (q + 64) with (q + -288 + 352) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHW : shw_ok [(q - 3296, q); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (6190348, 6190348 + 4)])
        by (unfold shw_ok; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_cons; [shw_P HP1w|]; apply Forall_cons; [shw_P HP2w|]; apply Forall_cons; [shw_P HP3w|]; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_nil);
      assert (IC2 : ictx T p lox qx mm) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| exact SHW]);
      assert (PX2 : pctx FA FN P1 P2 P3 mm) by (eapply pctx_frame; [exact PX| exact MU| exact SHW| exact FNW| exact HP1w| exact HP2w| exact HP3w]);
      eapply evt_cut;
      [ eapply vfscanf_i_spec with (q := (q + -288)%Z) (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := v3);
        [ unfold VF_DEPTH; replace (q + -288 - 48 - 2960) with (q + -3296) by lia; eassumption | assumption | exact FCv | exact APC | exact PC1 | exact PC2 | exact PC3
        | exact BY | split; [exact SSP1| exact SSP2] | exact ERR | exact HV | exact IC2 | exact PX2
        | unfold VF_DEPTH; lia | lia | clear - Q16; Z.div_mod_to_equations; lia ]
      | unfold vfi_post, vfi_W, VF_DEPTH, ERRNOA; post_call asegs mm ] end.
    clear IC2 PX2 SSP1 SSP2 APC.
    lazymatch goal with H : ssp_cells _ canary |- _ => destruct H as [SSP1 SSP2]; unfold got_ssp, ssp_guard in SSP1, SSP2 end.
    do 3 zstep.
    rewrite bv_eqb_refl. cbn [negb].
    do 7 zstep.
    lazymatch goal with P : stk asegs ?mm _ (q + -288) |- _ =>
      replace (q + -288 - 48 - 2960) with (q - 3296) in P by lia;
      pose proof (stk_merge _ _ _ _ _ P STJ ltac:(lia)) as ST5; clear P STJ end.
    lazymatch goal with H : rw_cells asegs _ (q + -288 + 8) [CB 232 _] |- _ => release_frame H ST5 (q + -48)%Z end.
    release_frame FRV ST5 q.
    replace (q + -288 + 352) with (q + 64) in * by lia.
    unfold vs_post, vs_W, VS_DEPTH, ERRNOA, ssp_cells, got_ssp, ssp_guard.
    finish.
    all: eassumption.
  Qed.

  Definition A0_sscanf_i : Z := 0x44148.
  Definition SSI_DEPTH : Z := 3408.
  Definition ssi_W (q : Z) : list ivl := [(q - SSI_DEPTH, q); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (ERRNOA, ERRNOA + 4)].
  Definition ssi_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev v1 v2 v3 : word),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (ssi_W q) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (q - SSI_DEPTH) q
      /\ bytes_at asegs m' T (zbytes txt) /\ ssp_cells m' canary
      /\ rw_cells asegs m' ERRNOA [C4 ev]
      /\ rw_cells asegs m' P1 [C4 v1] /\ rw_cells asegs m' P2 [C4 v2] /\ rw_cells asegs m' P3 [C4 v3].

  #[using="pre post fmtl ds' W3num w3n SC FMD FMB HFA FMR FE HNC HW3 HAP3 FNW TXT Hp T0 TLO HP1 HP2 HP3 PSEP HP1w HP2w HP3w IW TPV"] Lemma sscanf_i_spec : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ev v1 v2 v3 : word) (r : Z),
    stk asegs m (q - SSI_DEPTH) q -> mem_inv asegs m ->
    rw_cells asegs m P1 [C4 v1] -> rw_cells asegs m P2 [C4 v2] -> rw_cells asegs m P3 [C4 v3] ->
    bytes_at asegs m T (zbytes txt) -> ssp_cells m canary -> rw_cells asegs m ERRNOA [C4 ev] ->
    sscanf_model fmtd txt p = Some r ->
    ictx T p lox qx m -> pctx FA FN P1 P2 P3 m ->
    lox <= q - SSI_DEPTH -> q <= qx -> q mod 16 = 0 ->
    evt asegs (ssi_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz T) (wz FA) (wz P1) (wz P2) a4w a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A0_sscanf_i) fc None m (seg_rom asegs)).
  Proof.
    intros until r. intros ST MI PC1 PC2 PC3 BY SSP ERR HV IC PX LOX QXQ Q16.
    pose proof IW as IW'. destruct IW' as (CWT & W2T & NST & KLOX & LQX & QX47 & TPLO & TPHI).
    pose proof (munch_refl (ssi_W q) m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold ssi_W, SSI_DEPTH, ERRNOA in MU. unfold SSI_DEPTH in ST, LOX. unfold ERRNOA in ERR. unfold A0_sscanf_i.
    destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L40). unfold zlength in *.
    pose proof (zbytes_length txt) as LTX.
    assert (SHW : shw_ok [(q - 3408, q); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (6190348, 6190348 + 4)])
      by (unfold shw_ok; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_cons; [shw_P HP1w|]; apply Forall_cons; [shw_P HP2w|]; apply Forall_cons; [shw_P HP3w|]; apply Forall_cons; [cbn [fst snd]; lia|]; apply Forall_nil).
    zstep.
    carve_frame 24%nat ST. rename FR into FRH.
    carve_frame 24%nat ST. rename FR into APC.
    carve_frame 64%nat ST.
    do 16 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IC1 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| exact SHW]) end.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ (ictx_env _ _ _ _ _ IC1)) |].
    clear IC1.
    zstep. lit_branch. do 3 zstep.
    lazymatch goal with MUc : munch _ m ?m1, WMc : wmono asegs m ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IC1 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MUc| exact WMc| exact SHW]) end.
    call tryinit_spec; [assumption | eassumption | lia | lia | lia | exact (ie_inited _ (ictx_env _ _ _ _ _ IC1)) |].
    clear IC1.
    zstep. lit_branch.
    lazymatch goal with MUc : munch _ m ?m1, WMc : wmono asegs m ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (IC1 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MUc| exact WMc| exact SHW]) end.
    pose proof (ie_real_lib _ (ictx_env _ _ _ _ _ IC1)) as (_ & RL2 & _).
    do 7 zstep.
    replace (q + -48) with (q + -112 + 64) in * by lia.
    lazymatch goal with MUc : munch _ m ?mm, WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (IC2 : ictx T p lox qx mm) by (eapply ictx_frame; [exact IC| exact IW| exact MUc| exact WMc| exact SHW]);
      assert (PX2 : pctx FA FN P1 P2 P3 mm) by (eapply pctx_frame; [exact PX| exact MUc| exact SHW| exact FNW| exact HP1w| exact HP2w| exact HP3w]);
      eapply evt_cut;
      [ eapply vsscanf_spec with (q := (q + -112)%Z) (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := v3);
        [ unfold VS_DEPTH; replace (q + -112 - 3296) with (q - 3408) by lia; eassumption | assumption | exact APC | exact PC1 | exact PC2 | exact PC3
        | exact BY | split; [exact SSP1| exact SSP2] | exact ERR | exact HV | exact IC2 | exact PX2
        | unfold VS_DEPTH; lia | lia | clear - Q16; Z.div_mod_to_equations; lia ]
      | unfold vs_post, vs_W, VS_DEPTH, ERRNOA; post_call asegs mm ] end.
    clear IC1 IC2 PX2 RL2 SSP1 SSP2 APC.
    lazymatch goal with H : ssp_cells _ canary |- _ => destruct H as [SSP1 SSP2]; unfold got_ssp, ssp_guard in SSP1, SSP2 end.
    pose proof (model_range _ _ _ _ HV) as RR.
    zstep.
    assert (BL : bv_lts z64 (Z_to_bv 64 r) = (0 <? r)).
    { unfold bv_lts. pose proof (nconv_nonneg fmtd) as NN0. destruct HW3 as [[? _]|[? _]]; rewrite (SFModel.signed_of_Z r) by lia; reflexivity. }
    rewrite BL. clear BL.
    destruct (Z.ltb_spec 0 r) as [RP|RN]; cbn [negb].
    -
      do 8 zstep.
      pose proof SC as SC'. unfold scanf_common_gen in SC'.
      replace (q + -112 + 64) with (q + -48) in * by lia.
      lazymatch goal with MUc : munch _ m ?mm, WMc : wmono asegs m ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (IC3 : ictx T p lox qx mm) by (eapply ictx_frame; [exact IC| exact IW| exact MUc| exact WMc| exact SHW]);
        assert (PX3 : pctx FA FN P1 P2 P3 mm) by (eapply pctx_frame; [exact PX| exact MUc| exact SHW| exact FNW| exact HP1w| exact HP2w| exact HP3w]);
        destruct PX3 as ((AF & RF) & (A1 & R1) & (A2 & R2) & (A3 & R3));
        eapply evt_cut;
        [ eapply SC' with (AP := (q + -48)%Z) (P1 := P1) (P2 := P2) (P3 := P3) (r := r) (lo := (q + -112 - 3296)%Z) (w3 := a4w);
          [ assumption | exact (ictx_env _ _ _ _ _ IC3) | eassumption | lia | unfold SC_DEPTH; lia | lia
          | clear - Q16; Z.div_mod_to_equations; lia | pose proof (nconv_nonneg fmtd); lia
          | eassumption | exact HAP3 | lia | lia
          | exact AF | exact RF
          | exact A1 | exact R1 | exact HP1w | lia | exact A2 | exact R2 | exact HP2w | lia | exact A3 | exact R3 | exact HP3w | lia ]
        | post_call asegs mm ] end.
      clear SC'.
      do 7 zstep.
      lazymatch goal with P : stk asegs _ _ (q + -112) |- _ => replace (q + -112 - 3296) with (q - 3408) in P by lia; release_frame FR P (q + -48)%Z end.
      lazymatch goal with P : stk asegs _ _ (q + -48), A : rw_cells asegs _ (q + -48) _ |- _ => release_frame A P (q + -24)%Z; release_frame FRH P q end.
      unfold ssi_post, ssi_W, SSI_DEPTH, ERRNOA, ssp_cells, got_ssp, ssp_guard.
      finish.
      all: eassumption.
    -
      do 6 zstep.
      lazymatch goal with P : stk asegs _ _ (q + -112) |- _ => replace (q + -112 - 3296) with (q - 3408) in P by lia; release_frame FR P (q + -48)%Z end.
      replace (q + -112 + 64) with (q + -48) in * by lia.
      lazymatch goal with P : stk asegs _ _ (q + -48), A : rw_cells asegs _ (q + -48) _ |- _ => release_frame A P (q + -24)%Z; release_frame FRH P q end.
      unfold ssi_post, ssi_W, SSI_DEPTH, ERRNOA, ssp_cells, got_ssp, ssp_guard.
      finish.
      all: eassumption.
  Qed.
End SS.
