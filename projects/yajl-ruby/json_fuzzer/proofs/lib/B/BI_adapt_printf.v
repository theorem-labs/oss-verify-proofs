(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep ITree Nodes NodesCfg Decode SFModel PropExec MState Mem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad FmtFp StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzStdio TrzLeaf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel ITreeA NodesA ImplRzA MonadA TrzNodesA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model Printf_mlib Printf_pieces Printf_bridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BI_globals2 B_iface BI_iface BI_lowshadow BM_stdio_lib BX_file BX_trz BM_fwrite BX_Exit BX_adapt BI_adapt2 BI_adapt_fwrite BI_pcommon BP_policy BP_mjx BP_fwritex BP_printf_iface BP_vfprintf BP_fprintf1 BP_bridgeA BI_fprintf_icp BI_vprintf_icp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma bind_ret_unit_teq {St : Type} : forall (t : itree node (exc (unit * St))),
  TrzStdio.teq (ITree.bind node t (fun r => match r with Ok p => ITree.Ret (Ok (tt, snd p)) | Unr => ITree.Ret Unr end)) t.
Proof. aceil.
  induction t as [[|[[] s']] | n k IH]; cbn [ITree.bind snd]; try apply TrzStdio.teq_refl.
  constructor. intros x. apply IH.
Qed.

Lemma out_pieces_outsk {St} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St) :
  forall ps, out_pieces get_so set_so ps = outsk (stdout_fwritex get_so set_so) ps (mret tt).
Proof. aceil. induction ps as [|p ps IH]; [reflexivity|]. cbn [out_pieces outsk]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hsh_window : shw_lo C_SB alloc_ceiling = A_HSH_LO /\ shw_hi C_SB alloc_ceiling (2^47 - alloc_ceiling) = A_HSH_HI.
Proof.   (* [comment removed for export] *)
  split; [reflexivity|]. unfold shw_hi, al8, A_HSH_HI. replace (alloc_ceiling + (2^47 - alloc_ceiling) + -1) with (2^47 - 1) by lia. reflexivity.
Qed.

Lemma stack_shadow_zero_of_window : forall m ws,
  shadow_window bsegs m C_SB alloc_ceiling (2^47 - alloc_ceiling) ws -> ws = repeat (Z_to_bv 8 0) (length ws) ->
  stack_shadow_zero m.
Proof. aceil.
  intros m ws [(_ & _ & BA) LEN] E a Ha. pose proof hsh_window as [E1 E2]. rewrite E1, E2 in *.
  specialize (BA (Z.to_nat (a - A_HSH_LO)) ltac:(lia)).
  replace (A_HSH_LO + Z.of_nat (Z.to_nat (a - A_HSH_LO))) with a in BA by lia.
  rewrite BA, E. apply nth_error_repeat. lia.
Qed.

(* [comment removed for export] *)
Definition PRE_usage : list Z := str "usage: "%string.            Definition POST_usage : list Z := str " INPUT"%string ++ [10].
Definition PRE_cannot_open : list Z := str "cli: cannot open "%string. Definition POST_nl : list Z := [10].
Definition PRE_read_error : list Z := str "cli: read error on "%string.
Definition PRE_too_big : list Z := str "cli: input >= "%string.   Definition POST_too_big : list Z := str " bytes, refused"%string ++ [10].

Lemma fmt_usage_bytes : forall m, mem_inv bsegs m ->
  bytes_at bsegs m A_FMT_usage (zb (PRE_usage ++ 37 :: 115 :: POST_usage) ++ [Z_to_bv 8 0]).
Proof. aceil. intros m MI. apply ro_bytes_at; [exact MI | unfold A_FMT_usage; lia | unfold A_FMT_usage; cbn; lia |]. apply Image.ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_cannot_open_bytes : forall m, mem_inv bsegs m ->
  bytes_at bsegs m A_FMT_cannot_open (zb (PRE_cannot_open ++ 37 :: 115 :: POST_nl) ++ [Z_to_bv 8 0]).
Proof. aceil. intros m MI. apply ro_bytes_at; [exact MI | unfold A_FMT_cannot_open; lia | unfold A_FMT_cannot_open; cbn; lia |]. apply Image.ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_read_error_bytes : forall m, mem_inv bsegs m ->
  bytes_at bsegs m A_FMT_read_error (zb (PRE_read_error ++ 37 :: 115 :: POST_nl) ++ [Z_to_bv 8 0]).
Proof. aceil. intros m MI. apply ro_bytes_at; [exact MI | unfold A_FMT_read_error; lia | unfold A_FMT_read_error; cbn; lia |]. apply Image.ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_too_big_bytes : forall m, mem_inv bsegs m ->
  bytes_at bsegs m A_FMT_too_big (zb (PRE_too_big ++ 37 :: 117 :: POST_too_big) ++ [Z_to_bv 8 0]).
Proof. aceil. intros m MI. apply ro_bytes_at; [exact MI | unfold A_FMT_too_big; lia | unfold A_FMT_too_big; cbn; lia |]. apply Image.ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma fmt_emit_bytes : forall m, mem_inv bsegs m ->
  bytes_at bsegs m A_FMT_emit (zb ([] ++ 37 :: 100 :: POST_nl) ++ [Z_to_bv 8 0]).
Proof. aceil. intros m MI. apply ro_bytes_at; [exact MI | unfold A_FMT_emit; lia | unfold A_FMT_emit; cbn; lia |]. apply Image.ro_bytes_b_sound. vm_compute. reflexivity. Qed.

End RC__1.
Ltac lit_forall := cbn; repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Adapt.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.
Variables (aS : APS -> word -> Prop) (aN : APS -> nat) (aEB : APS -> Z).
Variable aalloc_same : APS -> APS -> Prop.
Notation C := ACONSTS.
Notation FM := AFMTS.

(* [comment removed for export] *)
Definition AHK_icp_stack_shadow0_stmt : Prop :=
  forall s LB LF m mo A n, AHK s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
    exists ws, shadow_window bsegs m C_SB A n ws /\ range_clean C_SB A n ws
               /\ pages_budgeted (aS s) (shw_lo C_SB A) (shw_hi C_SB A n)
               /\ ws = repeat (Z_to_bv 8 0) (length ws).

Hypothesis Hkip : AHK_kip_stmt C APS AHK aS aN aEB.
Hypothesis Hmi : AHK_mem_inv_stmt bsegs APS AHK.
Hypothesis Hso : AHK_so_stmt APS AHK SO.
Hypothesis Hglob : AHK_icp_globals_stmt bsegs APS AHK.
Hypothesis Hglob2 : AHK_icp_globals2_stmt APS AHK.
Hypothesis Hexit : AHK_icp_exit_stmt APS AHK SO aS.
Hypothesis Hupd : AHK_icp_stdio_upd_stmt APS AHK SO aS aN aEB aalloc_same.
Hypothesis Hlow : AHK_icp_lowpages_stmt APS AHK aS.
Hypothesis Hssz : AHK_icp_stack_shadow0_stmt.

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

(* [comment removed for export] *)
Lemma pol_of_bundle : forall s LB LF m mo, AHK s LB LF m mo ->
  let P := acc_ok (m_vm_lazy mo) (aS s) in
  POL_STACK P /\ POL_IMG P /\ POL_HSH P /\ POL_LSH P /\ POL_NUL P /\ stack_shadow_zero m.
Proof. aceil.
  intros s LB LF m mo HA. cbv zeta.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  assert (X1 : alloc_ceiling <= alloc_ceiling) by lia. assert (X2 : 1 <= 2^47 - alloc_ceiling) by (aceil; lia).
  assert (X3 : alloc_ceiling + (2^47 - alloc_ceiling) <= 2^47) by lia.   (* [comment removed for export] *)
  destruct (Hssz s LB LF m mo alloc_ceiling (2^47 - alloc_ceiling) HA X1 X2 X3) as (ws & SW & _ & PB & E).
  pose proof hsh_window as [E1 E2]. rewrite E1, E2 in PB. pose proof A_HSH_LO_range as HLR. unfold A_HSH_HI in HLR.
  split; [| split; [| split; [| split; [| split]]]].
  - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. unfold alloc_ceiling in *. lia.
  - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
  - intros a k H1 H2. right. eapply (pages_budgeted_acc_inS _ A_HSH_LO A_HSH_HI); [exact PB | unfold A_HSH_HI in *; lia | exact H1 | exact H2 | unfold A_HSH_HI in *; lia].
  - intros a k H1 H2. right. eapply (pages_budgeted_acc_inS _ 0x7fff7000 0x8fff7000); [eapply (Hlow _ _ _ _ _ _ _ HA); lia | lia | exact H1 | exact H2 | lia].
  - intros a. right. split; [| intros k Hk; cbn in Hk; lia]. unfold acc_nowrap. cbn [fst snd].
    pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as X. unfold bv_modulus in X. cbn in X. lia.
  - exact (stack_shadow_zero_of_window m ws SW E).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afprintf_gen :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet) (A : Z) (pre post : list Z) (c : Z) (args : list parg) (ps : list (list Z)) (r : Z) (zs : list Z),
  let fmt := pre ++ 37 :: c :: post in
  let q := usp sp in
  K [] -> AHK s LB LF m mo ->
  Forall (fun x => 0 < x < 256 /\ x <> 37) pre -> Forall (fun x => 0 < x < 256 /\ x <> 37) post ->
  (c = 115 \/ c = 100 \/ c = 117) -> zlength fmt <= 63 -> 0x10000 <= A -> A + 64 <= 0x21000 ->
  bytes_at bsegs m A (zb fmt ++ [Z_to_bv 8 0]) -> pass1_ok (fmt ++ [0]) = true ->
  args_ok RSTDERR (q - 112 - 352) 80 m lo q (q - 112 - VF_FRAME) [a2; a3; a4; a5; a6; a7] args ->
  printf_pieces (fmt ++ [0]) args = Some (ps, r) -> fp_calls (length (fmt ++ [0])) (fmt ++ [0]) args = [] ->
  sp_ok (length (fmt ++ [0])) (fmt ++ [0]) args ->
  Forall (fun p => zlength p + INTERNAL_BUFSIZ <= WRITEV_MAX) ps ->
  (c = 115 -> bytes_at bsegs m (bv_unsigned a2) (zb zs ++ [Z_to_bv 8 0]) /\ Forall (fun x => 0 < x < 256) zs
              /\ q <= bv_unsigned a2 /\ bv_unsigned a2 + zlength zs + 1 < A_STK_HI /\ zlength zs + 1 < 2^40) ->
  stk bsegs m lo q -> alloc_ceiling <= lo -> lo <= q - AICP_STACK -> q <= 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz (c_stderr_F C) -> a1 = wz A ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     stk bsegs m' lo q -> munch [(lo, q); (c_stderr_F C, c_stderr_F C + 232)] m m' -> wmono bsegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_fprintf C)) fc None m (seg_rom bsegs)) mo)
            (ShapeAlg.t_emit (Wz 2 (concat ps)) K).
Proof. aceil.
  intros until zs. cbv zeta. intros HK0 HA HPRE HPOST HC FL HA0 HA1 FMT P1 AOK PP FPC SPOK HW HS ST LOC LO SPTOP HTP FRM -> -> HK.
  cbv beta. unfold AICP_STACK in LO.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  pose proof (Hglob _ _ _ _ _ HA) as G. pose proof (Hglob2 _ _ _ _ _ HA) as G2.
  destruct (Hexit _ _ _ _ _ HA) as (_ & (guard & cdt & thr & sec & tm1 & SS) & LS & _ & _ & LDS & LDI).
  destruct SS as (STAT & SIN & SOF & SEF & SSP).
  pose proof (pol_of_bundle _ _ _ _ _ HA) as (PSTK & PIMG & PHSH & PLSH & PNUL & SSZ).
  set (P := acc_ok (m_vm_lazy mo) (aS s)) in *.
  assert (MJ : mjx m) by (split; [exact G | split; [exact G2 | split; [exact LS | exact SSZ]]]).
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil.
  assert (IM : implMA bsegs P (outsk OUT_stderr ps (FLUSH_stderr (St:=stdout_st))) ([], SO s)
                 (fun _ bs ms' => fprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo guard m (snd bs) ms')
                 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xa9c68) (wz A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x42ff8) fc None m (seg_rom bsegs))).
  { unfold implMA. eapply implA_evtA. { stepA. apply evtA_done. eapply eq_refl. } cbv beta. intros ms' <-.
    pose proof (fprintf_icp_spec (St:=stdout_st) P PSTK PIMG PHSH PLSH PNUL) as SPEC. cbv zeta in SPEC. unfold fprintf_icp_entry in SPEC.
    eapply SPEC with (pre := pre) (c := c) (post := post) (args := args) (zs := zs); clear SPEC.
    all: try reflexivity.
    all: first [ exact (stderr_wfile0_wfile _ SEF) | exact FMT | exact HPRE | exact HPOST | exact HC | exact FL | exact HA0 | exact HA1
               | exact P1 | exact AOK | exact PP | exact FPC | exact SPOK | exact HS | exact ST
               | exact LOC | unfold A_CEIL; lia | unfold FPRINTF_ICP_DEPTH; lia | unfold A_STK_HI; lia
               | exact SSP | exact MI | exact FRM | exact MJ ].
  }
  unfold implMA in IM.
  (* [comment removed for export] *)
  lazymatch type of IM with implA _ _ _ _ _ ?ms0 =>
  assert (IM2 : implA bsegs (NodesA.at_nodeA bsegs) P (stderr_fprintf ps (SO s))
                  (epost (fun p ms' => fprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo guard m (snd p) ms' /\ snd p = SO s)) ms0)
  end.
  { unfold stderr_fprintf.
    eapply implA_epost_mono.
    - eapply (stderr_bridgeA P ps [] (SO s) (fun s' ms' => fprintf_icp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo guard m s' ms' /\ s' = SO s)).
      eapply implA_mono; [eapply (implA_tforall bsegs (NodesA.at_nodeA bsegs) P _ _ _ _ (outsk_flush_leavesA ps [] (SO s))); exact IM|].
      intros [|[[] [b s']]] ms' [H1 H2]; cbn in H1, H2 |- *; [exact I|]. split; [exact H1 | exact H2].
    - intros [[] s'] ms' H'. exact H'. }
  clear IM.
  eapply (implA_trzA_srealizes bsegs (aS s) (aN s) (aEB s) P (stderr_fprintf ps (SO s)) _ _ mo mo (fun _ _ => K) _ IM2).
  - apply (trzA_stderr_fprintf ps (SO s) mo (fun _ _ => K) (conj Hminv Hh) HW (fun _ _ => HK0)).
  - apply mequiv_refl.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - intros rr ms' mot' moa' Q L Heq HKP.
    apply (leaf_stderr_fprintf_ok ps (SO s)) in L as [-> ->]; [| exact HW].
    cbn [epost fst snd] in Q. destruct Q as [Q _]. unfold fprintf_icp_post in Q.
    destruct Q as (x5 & x6 & x7 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SEF1 & SSP1 & MJ1).
    (* [comment removed for export] *)
    assert (SS1 : stdio_state m' (SO s) guard cdt thr sec tm1).
    { split; [| split; [| split; [| split; [exact SEF1 | exact SSP1]]]].
      - destruct STAT as (L1 & L2 & L3 & L4 & L5). unfold stdio_statics.
        split; [eapply rw_cells_transport; [exact L1 | exact MU | exact WM | cbn; lia] |].
        split; [eapply rw_cells_transport; [exact L2 | exact MU | exact WM | cbn; lia] |].
        split; [eapply rw_cells_transport; [exact L3 | exact MU | exact WM | cbn; lia] |].
        split; [eapply rw_cells_transport; [exact L4 | exact MU | exact WM | cbn; lia]
              | eapply rw_cells_transport; [exact L5 | exact MU | exact WM | cbn; lia] ].
      - unfold stdin_file, stdin_cells in *. eapply rw_cells_transport; [exact SIN | exact MU | exact WM | cbn; lia].
      - destruct SOF as (fl & md & tl & bb & FC & R1 & BUF & R2). exists fl, md, tl, bb. unfold file_cells in *.
        split; [eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn; lia]|].
        split; [exact R1|]. split; [eapply rw_cells_transport; [exact BUF | exact MU | exact WM | cbn; lia]| exact R2]. }
    destruct (Hupd s LB LF m mo m' _ (SO s) guard cdt thr sec tm1 HA MU WM MI'
                ltac:(constructor; [left; unfold aclient_write_ok; cbn [fst snd]; left; aceil; lia |];
                      constructor; [right; unfold stdio_ivs; cbn; left; reflexivity | constructor])
                SS1 (Hso _ _ _ _ _ HA)) as (s' & HA' & SO' & SAME & EaS & EaN & EaEB).
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA') as (_ & _ & _ & _ & MAG').
    rewrite <- EaS, <- EaN, <- EaEB in HLIa.
    pose proof (MAG' moa' Hag HLIa) as HA''.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fc' m' moa' s').
    + exact ST'.
    + cbn [c_stderr_F ACONSTS]. exact MU.
    + exact WM. + exact FRM'. + exact HA''. + exact SAME. + exact SO'.
    + exact Efs. + exact Efds.
    + exact Hag.
Qed.

(* [comment removed for export] *)
Definition adiag_args2 (d : diag_msg) (m : mem) (fmtp argw : word) (lo SP : Z) : Prop :=
  match d with
  | DUsage zs | DCannotOpen zs | DReadError zs =>
      fmtp = wz (match d with DUsage _ => f_usage FM | DCannotOpen _ => f_cannot_open FM | _ => f_read_error FM end)
      /\ (exists slack : list byte, bytes_at bsegs m (bv_unsigned argw) (zb zs ++ Z_to_bv 8 0 :: slack)
                                    /\ (- (bv_unsigned argw + zlength zs + 1)) mod 8 <= zlength slack)
      /\ Forall (fun c => 0 < c < 256) zs /\ zlength zs < 2^20
      /\ SP <= bv_unsigned argw /\ bv_unsigned argw + zlength zs + 16 <= 2^47
  | DTooBig => fmtp = wz (f_too_big FM) /\ bv_unsigned argw mod 2^32 = 67108864
  | _ => False
  end.

(* [comment removed for export] *)
Lemma diag_s_args : forall m (argw a3 a4 a5 a6 a7 : word) (zs : list Z) (lo q : Z) slack,
  bytes_at bsegs m (bv_unsigned argw) (zb zs ++ Z_to_bv 8 0 :: slack) -> (- (bv_unsigned argw + zlength zs + 1)) mod 8 <= zlength slack ->
  Forall (fun c => 0 < c < 256) zs -> zlength zs < 2^20 -> q <= bv_unsigned argw -> bv_unsigned argw + zlength zs + 16 <= 2^47 ->
  alloc_ceiling <= q ->
  (bytes_at bsegs m (bv_unsigned argw) (zb zs ++ [Z_to_bv 8 0]) /\ Forall (fun x => 0 < x < 256) zs
     /\ q <= bv_unsigned argw /\ bv_unsigned argw + zlength zs + 1 < A_STK_HI /\ zlength zs + 1 < 2^40)
  /\ args_ok RSTDERR (q - 112 - 352) 80 m lo q (q - 112 - VF_FRAME) [argw; a3; a4; a5; a6; a7] [PA_s zs].
Proof. aceil.
  intros m argw a3 a4 a5 a6 a7 zs lo q slack BY SLK HF LEN QA HI CQ.
  pose proof (zlength_nonneg' zs) as Z0.
  assert (BY0 : bytes_at bsegs m (bv_unsigned argw) (zb zs ++ [Z_to_bv 8 0])).
  { replace (zb zs ++ Z_to_bv 8 0 :: slack) with ((zb zs ++ [Z_to_bv 8 0]) ++ slack) in BY by (rewrite <- app_assoc; reflexivity).
    exact (proj1 (proj1 (bytes_at_app bsegs _ _ _ _) BY)). }
  set (k := (- (bv_unsigned argw + zlength zs + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
  set (slack' := firstn (Z.to_nat k) slack).
  assert (LS' : zlength slack' = k) by (subst slack'; unfold zlength in *; rewrite length_firstn; lia).
  assert (BY' : bytes_at bsegs m (bv_unsigned argw) (zb zs ++ Z_to_bv 8 0 :: slack')).
  { rewrite <- (firstn_skipn (Z.to_nat k) slack) in BY.
    replace (zb zs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) slack ++ skipn (Z.to_nat k) slack)
      with ((zb zs ++ Z_to_bv 8 0 :: slack') ++ skipn (Z.to_nat k) slack) in BY by (subst slack'; rewrite <- app_assoc; reflexivity).
    exact (proj1 (proj1 (bytes_at_app bsegs _ _ _ _) BY)). }
  aceil.
  split.
  - unfold A_STK_HI. split; [exact BY0|]. split; [exact HF|]. lia.
  - cbn [args_ok arg_ok]. split; [| exact I]. exists slack'. unfold VF_FRAME.
    split; [exact BY'|]. split; [exact HF|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    left. unfold in_stackw, A_STK_HI. change A_CEIL with alloc_ceiling. clear BY BY0 BY' HF. lia.
Qed.

Lemma afprintf_diag_rz :
  forall (d : diag_msg) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet),
  K [] -> AHK s LB LF m mo ->
  adiag_args2 d m a1 a2 lo (usp sp) ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> usp sp <= 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz (c_stderr_F C) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     stk bsegs m' lo (usp sp) -> munch [(lo, usp sp); (c_stderr_F C, c_stderr_F C + 232)] m m' -> wmono bsegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_fprintf C)) fc None m (seg_rom bsegs)) mo)
            (ShapeAlg.t_emit (Wz 2 (concat (adiag_pieces d))) K).
Proof. aceil.
  intros until K. intros HK0 HA DA ST LOC LO SPTOP HTP FRM HA0 HK.
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  assert (CQ : alloc_ceiling <= usp sp) by (unfold AICP_STACK in LO; lia).
  destruct d as [zs | zs | zs | | | |]; cbn [adiag_args2 f_usage f_cannot_open f_read_error f_too_big AFMTS] in DA;
    try contradiction; cbn [adiag_pieces].
  - destruct DA as (Ha1 & (slack & BY & SLK) & HF & LEN & QA & HI).
    destruct (diag_s_args m a2 a3 a4 a5 a6 a7 zs lo (usp sp) slack BY SLK HF LEN QA HI CQ) as [HS AOK].
    apply (afprintf_gen ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF lo K
              A_FMT_usage PRE_usage POST_usage 115 [PA_s zs] (pieces_usage zs) (14 + zlength zs) zs);
      [ exact HK0 | exact HA | lit_forall | lit_forall | left; reflexivity | unfold zlength; cbn; lia
      | unfold A_FMT_usage; lia | unfold A_FMT_usage; lia | exact (fmt_usage_bytes m MI) | vm_compute; reflexivity | exact AOK
      | replace ((PRE_usage ++ 37 :: 115 :: POST_usage) ++ [0]) with FMT_usage by (vm_compute; reflexivity); apply printf_pieces_usage; unfold INT_MAX; lia
      | vm_compute; reflexivity | vm_compute; repeat first [split | reflexivity | exact I]
      | unfold pieces_usage, INTERNAL_BUFSIZ, WRITEV_MAX; repeat (apply Forall_cons; [unfold zlength in *; cbn; lia|]); apply Forall_nil
      | intros _; exact HS
      | exact ST | exact LOC | exact LO | exact SPTOP | exact HTP | exact FRM | exact HA0 | exact Ha1 | exact HK ].
  - destruct DA as (Ha1 & (slack & BY & SLK) & HF & LEN & QA & HI).
    destruct (diag_s_args m a2 a3 a4 a5 a6 a7 zs lo (usp sp) slack BY SLK HF LEN QA HI CQ) as [HS AOK].
    apply (afprintf_gen ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF lo K
              A_FMT_cannot_open PRE_cannot_open POST_nl 115 [PA_s zs] (pieces_cannot_open zs) (18 + zlength zs) zs);
      [ exact HK0 | exact HA | lit_forall | lit_forall | left; reflexivity | unfold zlength; cbn; lia
      | unfold A_FMT_cannot_open; lia | unfold A_FMT_cannot_open; lia | exact (fmt_cannot_open_bytes m MI) | vm_compute; reflexivity | exact AOK
      | replace ((PRE_cannot_open ++ 37 :: 115 :: POST_nl) ++ [0]) with FMT_cannot_open by (vm_compute; reflexivity); apply printf_pieces_cannot_open; unfold INT_MAX; lia
      | vm_compute; reflexivity | vm_compute; repeat first [split | reflexivity | exact I]
      | unfold pieces_cannot_open, INTERNAL_BUFSIZ, WRITEV_MAX; repeat (apply Forall_cons; [unfold zlength in *; cbn; lia|]); apply Forall_nil
      | intros _; exact HS
      | exact ST | exact LOC | exact LO | exact SPTOP | exact HTP | exact FRM | exact HA0 | exact Ha1 | exact HK ].
  - destruct DA as (Ha1 & (slack & BY & SLK) & HF & LEN & QA & HI).
    destruct (diag_s_args m a2 a3 a4 a5 a6 a7 zs lo (usp sp) slack BY SLK HF LEN QA HI CQ) as [HS AOK].
    apply (afprintf_gen ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF lo K
              A_FMT_read_error PRE_read_error POST_nl 115 [PA_s zs] (pieces_read_error zs) (20 + zlength zs) zs);
      [ exact HK0 | exact HA | lit_forall | lit_forall | left; reflexivity | unfold zlength; cbn; lia
      | unfold A_FMT_read_error; lia | unfold A_FMT_read_error; lia | exact (fmt_read_error_bytes m MI) | vm_compute; reflexivity | exact AOK
      | replace ((PRE_read_error ++ 37 :: 115 :: POST_nl) ++ [0]) with FMT_read_error by (vm_compute; reflexivity); apply printf_pieces_read_error; unfold INT_MAX; lia
      | vm_compute; reflexivity | vm_compute; repeat first [split | reflexivity | exact I]
      | unfold pieces_read_error, INTERNAL_BUFSIZ, WRITEV_MAX; repeat (apply Forall_cons; [unfold zlength in *; cbn; lia|]); apply Forall_nil
      | intros _; exact HS
      | exact ST | exact LOC | exact LO | exact SPTOP | exact HTP | exact FRM | exact HA0 | exact Ha1 | exact HK ].
  - destruct DA as [Ha1 Hu]. pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    apply (afprintf_gen ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo s LB LF lo K
              A_FMT_too_big PRE_too_big POST_too_big 117 [PA_u 67108864] pieces_too_big 38 []);
      [ exact HK0 | exact HA | lit_forall | lit_forall | right; right; reflexivity | unfold zlength; cbn; lia
      | unfold A_FMT_too_big; lia | unfold A_FMT_too_big; lia | exact (fmt_too_big_bytes m MI) | vm_compute; reflexivity
      | cbn [args_ok arg_ok]; split; [split; [lia | exact Hu] | exact I]
      | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; repeat first [split | reflexivity | exact I]
      | unfold pieces_too_big, INTERNAL_BUFSIZ, WRITEV_MAX; repeat (apply Forall_cons; [unfold zlength; cbn; lia|]); apply Forall_nil
      | intros X; exfalso; lia
      | exact ST | exact LOC | exact LO | exact SPTOP | exact HTP | exact FRM | exact HA0 | exact Ha1 | exact HK ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma trzA_stdout_vprintf : forall ps (so : stdout_st) mo (K : exc (unit * stdout_st) -> Model -> TSet),
  mokA mo -> zlength (so_buf so) <= STDOUT_BUFSIZ -> Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) ps ->
  K (Ok (tt, snd (vprintf_pure so ps))) mo [] ->
  trzA (stdout_vprintf so_get so_set ps so) mo K (t_emit (Wz 1 (fst (vprintf_pure so ps))) (K (Ok (tt, snd (vprintf_pure so ps))) mo)).
Proof. aceil.
  intros ps so mo K Hok Hb Hps HK.
  eapply trzA_teq; [| apply (bind_ret_unit_teq (stdout_vprintf so_get so_set ps so))].
  change (ITree.bind node (stdout_vprintf so_get so_set ps so) (fun r => match r with Ok p => ITree.Ret (Ok (tt, snd p)) | Unr => ITree.Ret Unr end))
    with (mbind (stdout_vprintf so_get so_set ps) (fun _ => mret tt) so).
  apply (trzA_stdout_vprintf_k so_get so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) ps (fun _ => mret tt) so mo K _ Hok Hb Hps);
    [| exact HK | intros x; reflexivity].
  apply trzA_mret.
Qed.

Lemma pieces_emit_0_small : Forall (fun p => zlength p + STDOUT_BUFSIZ <= WRITEV_MAX) (pieces_emit_d 0).
Proof. aceil. cbn. unfold STDOUT_BUFSIZ, WRITEV_MAX. repeat (apply Forall_cons; [unfold zlength; cbn; lia|]). apply Forall_nil. Qed.

#[local] Unset Kernel Term Sharing.   (* [comment removed for export] *)
Lemma aprintf_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (ap lo : Z) (v1 : word) (K : TSet),
  K [] -> AHK s LB LF m mo ->
  rw_cells bsegs m ap [C8 v1] -> bv_unsigned v1 mod 2^32 = 0 -> usp sp <= ap -> ap + 56 < 2^47 -> ap mod 8 = 0 ->
  zlength (so_buf (SO s)) <= STDOUT_BUFSIZ ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> usp sp <= 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz (f_emit FM) -> a1 = wz ap ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     stk bsegs m' lo (usp sp) -> munch [(lo, usp sp); (c_stdout_F C, c_stdout_F C + 232); (c_stdout_buf C, c_stdout_buf C + 1024)] m m' -> wmono bsegs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = snd (vprintf_pure (SO s) (pieces_emit_d 0)) -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_vprintf C)) fc None m (seg_rom bsegs)) mo)
            (ShapeAlg.t_emit (Wz 1 (fst (vprintf_pure (SO s) (pieces_emit_d 0)))) K).
Proof. aceil.
  intros until K. intros HK0 HA VAC HV1 QAP APHI AP8 HB ST LOC LO SPTOP HTP FRM -> -> HK.
  cbv beta. unfold AICP_STACK in LO. cbn [f_emit AFMTS].
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  pose proof (Hglob _ _ _ _ _ HA) as G. pose proof (Hglob2 _ _ _ _ _ HA) as G2.
  destruct (Hexit _ _ _ _ _ HA) as (_ & (guard & cdt & thr & sec & tm1 & SS) & LS & _ & _ & LDS & LDI).
  destruct SS as (STAT & SIN & SOF & SEF & SSP).
  pose proof (pol_of_bundle _ _ _ _ _ HA) as (PSTK & PIMG & PHSH & PLSH & PNUL & SSZ).
  set (P := acc_ok (m_vm_lazy mo) (aS s)) in *.
  assert (MJ : mjx m) by (split; [exact G | split; [exact G2 | split; [exact LS | exact SSZ]]]).
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil.
  pose proof (BI_pcommon.rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 v1 ++ []) with (u64s [v1]) in VAA.
  set (ps := pieces_emit_d 0).
  (* [comment removed for export] *)
  assert (IM : implMA bsegs P (stdout_vprintf so_get so_set ps) (SO s)
                 (vprintf_icp_post so_get ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo guard m)
                 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_FMT_emit) (wz ap) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x42fec) fc None m (seg_rom bsegs))).
  { unfold stdout_vprintf. rewrite (out_pieces_outsk so_get so_set).
    unfold implMA. eapply implA_evtA. { stepA. apply evtA_done. eapply eq_refl. } cbv beta. intros ms' <-.
    pose proof (vprintf_icp_spec (St:=stdout_st) so_get so_set P PSTK PIMG PHSH PLSH PNUL (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)) as SPEC.
    cbv zeta in SPEC. unfold vprintf_icp_entry in SPEC.
    apply (SPEC ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (SO s)
             A_FMT_emit ap [] POST_nl 100 [v1] [PA_i 0] ps 2 lo guard); clear SPEC;
      [ reflexivity | reflexivity | exact SOF | exact (fmt_emit_bytes m MI) | apply Forall_nil | lit_forall | left; reflexivity
      | unfold zlength; cbn; lia | unfold A_FMT_emit; lia | unfold A_FMT_emit; lia | vm_compute; reflexivity
      | exact VAA
      | cbn [args_ok arg_ok]; split; [split; [lia | rewrite HV1; reflexivity] | exact I]
      | subst ps; vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; repeat first [split | reflexivity | exact I]
      | lia | unfold A_STK_HI, zlength; cbn [length]; lia | unfold A_STK_HI; lia
      | exact ST | exact LOC | unfold VPRINTF_ICP_DEPTH; lia | unfold A_STK_HI; lia
      | exact SSP | exact MI | exact FRM | exact MJ ]. }
  unfold implMA in IM.
  eapply (implA_trzA_srealizes bsegs (aS s) (aN s) (aEB s) P (stdout_vprintf so_get so_set ps (SO s)) _ _ mo mo (fun _ _ => K) _ IM).
  - apply (trzA_stdout_vprintf ps (SO s) mo (fun _ _ => K) (conj Hminv Hh) HB pieces_emit_0_small HK0).
  - apply mequiv_refl.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - intros rr ms' mot' moa' Q L Heq HKP.
    apply (leaf_stdout_vprintf_ok so_get so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) ps (SO s)) in L as [-> ->];
      [| exact HB | exact pieces_emit_0_small | intros x; reflexivity].
    cbn [epost fst snd] in Q. unfold vprintf_icp_post in Q.
    destruct Q as (x5 & x6 & x7 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SOF1 & SSP1 & MJ1).
    unfold so_get, so_set in SOF1. subst ps.
    set (so' := snd (vprintf_pure (SO s) (pieces_emit_d 0))) in *.
    (* [comment removed for export] *)
    assert (SS1 : stdio_state m' so' guard cdt thr sec tm1).
    { split; [| split; [| split; [exact SOF1 | split; [| exact SSP1]]]].
      - destruct STAT as (L1 & L2 & L3 & L4 & L5). unfold stdio_statics.
        split; [eapply rw_cells_transport; [exact L1 | exact MU | exact WM | cbn; lia] |].
        split; [eapply rw_cells_transport; [exact L2 | exact MU | exact WM | cbn; lia] |].
        split; [eapply rw_cells_transport; [exact L3 | exact MU | exact WM | cbn; lia] |].
        split; [eapply rw_cells_transport; [exact L4 | exact MU | exact WM | cbn; lia]
              | eapply rw_cells_transport; [exact L5 | exact MU | exact WM | cbn; lia] ].
      - unfold stdin_file, stdin_cells in *. eapply rw_cells_transport; [exact SIN | exact MU | exact WM | cbn; lia].
      - destruct SEF as (fl & md & e & we & tl & FC & R1 & R2 & R3). exists fl, md, e, we, tl. unfold file_cells in *.
        split; [eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn; lia]|]. split; [exact R1|]. split; [exact R2| exact R3]. }
    assert (BUF1 : zlength (so_buf so') <= STDOUT_BUFSIZ).
    { destruct SOF1 as (fl & md & tl & bb & _ & _ & _ & _ & B & _). unfold STDOUT_BUFSIZ. exact B. }
    assert (MU' : munch [(lo, usp sp); (0xa9d58, 0xa9d58 + 232); (0x601c58, 0x602060)] m m').
    { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros; lia. }
    assert (FW : Forall (fun iv => aclient_write_ok C LB iv \/ In iv stdio_ivs) [(lo, usp sp); (0xa9d58, 0xa9d58 + 232); (0x601c58, 0x602060)]).
    { constructor; [left; unfold aclient_write_ok; cbn [fst snd]; left; aceil; lia |].
      constructor; [right; unfold stdio_ivs; cbn; right; left; reflexivity |].
      constructor; [right; unfold stdio_ivs; cbn; right; right; left; reflexivity | constructor]. }
    destruct (Hupd s LB LF m mo m' _ so' guard cdt thr sec tm1 HA MU' WM MI' FW SS1 BUF1) as (s' & HA' & SO' & SAME & EaS & EaN & EaEB).
    pose proof (mequiv_magree _ _ Heq) as Hag.
    destruct HKP as [[HLIa _] _].
    destruct (Hkip _ _ _ _ _ HA') as (_ & _ & _ & _ & MAG').
    rewrite <- EaS, <- EaN, <- EaEB in HLIa.
    pose proof (MAG' moa' Hag HLIa) as HA''.
    pose proof (magree_frame _ _ Hag) as (Efds & _ & _ & Efs & _).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fc' m' moa' s').
    + exact ST'.
    + cbn [c_stdout_F c_stdout_buf ACONSTS]. exact MU.
    + exact WM. + exact FRM'. + exact HA''. + exact SAME. + exact SO'.
    + exact Efs. + exact Efds.
    + exact Hag.
Qed.

(* [comment removed for export] *)
Lemma afprintf_diag_proof : afprintf_diag_stmt bsegs C FM APS AHK SO aalloc_same.
Proof.
  hnf. intros until K. intros HK0 HA DA ST LOC LO SPTOP HTP FRM HA0 HK.
  eapply afprintf_diag_rz; [exact HK0 | exact HA | exact DA | exact ST | exact LOC | exact LO | clear -SPTOP; lia | exact HTP | exact FRM | exact HA0 | exact HK].
Qed.
Lemma aprintf_proof : aprintf_rz_stmt bsegs C FM APS AHK SO aalloc_same.
Proof.
  hnf. intros until K. intros HK0 HA VAC HV1 QAP APHI AP8 HB ST LOC LO SPTOP HTP FRM HA0 HA1 HK.
  eapply aprintf_rz; [exact HK0 | exact HA | exact VAC | exact HV1 | exact QAP | exact APHI | exact AP8 | exact HB | exact ST | exact LOC | exact LO
                    | clear -SPTOP; lia | exact HTP | exact FRM | exact HA0 | exact HA1 | exact HK].
Qed.
End Adapt.
End RC__2.
