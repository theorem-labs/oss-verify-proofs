(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio Canon ProgDetTarget.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Pj_loc_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow X_bridge X_bridge2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx Sj_acps R_m2s R_setshadow R_poison FX_Layout FX_Exit FX_Stdio_iface F_stdio_write I_iodefs F_fwrite I_fwrite X_aexdefs X_atexit X_xdefs X_unreg X_fini X_exitw X_ixdefs X_ixdefs2 X_atcxa X_vecxdefs X_xiface Imp_ios_defsA Imp_xifaceA Imp_ios_exitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition so_id (so : stdout_st) : stdout_st := so.
Definition so_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.

Lemma TT_exit_flush : forall (so : stdout_st) (T : TSet),
  (so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 -> T [] ->
  t_eq (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => T)) (t_emit (evw 1 (so_buf so)) T).
Proof.
  intros so T H Hl HT. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  unfold so_id at 1.
  destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
  - destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
    unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
    unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
    rewrite TT_ebind. cbn [TT]. unfold so_id. unfold stdio_writev.
    assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
    rewrite (iov_start_cons (so_buf so) [] NE).
    eapply t_eq_trans.
    { apply (TT_wv_loop (WV_FUEL [so_buf so; []]) 1 [so_buf so; []] so (fun _ => T)); [cbn; lia| | | exact HT];
        unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia. }
    cbn [concat]. rewrite app_nil_r. rewrite <- evw_to_bytes. apply t_eq_refl.
  - assert (E : so_buf so = []) by (destruct (so_buf so); [reflexivity| cbn in Ge; unfold zlength in Ge; cbn in Ge; lia]).
    rewrite E. cbn [TT evw map]. apply t_eq_sym, t_emit_nil_eq. exact HT.
Qed.

Lemma tok_exit_flush : forall (so : stdout_st),
  (so_first so = false \/ so_buf so = []) -> zlength (so_buf so) <= 2^26 ->
  tok [1] ((stdout_exit_flush so_id so_set : @M stdout_st unit) so).
Proof.
  intros so H Hl. unfold stdout_exit_flush, rd_so, mbind, mget, mret. cbn [ebind bind fst snd].
  unfold so_id at 1.
  destruct (Z.ltb_spec 0 (zlength (so_buf so))) as [Lt|Ge].
  - destruct H as [Hf|Hb]; [| rewrite Hb in Lt; unfold zlength in Lt; cbn in Lt; lia].
    unfold stdout_writefn, rd_so, mbind, mget, mret. cbn [ebind bind fst snd]. unfold so_id at 1. rewrite Hf.
    unfold stdout_stdio_write, rd_so, mbind, mget, mret, upd_so, mupd. cbn [ebind bind fst snd].
    apply tok_ebind; [| intros x; exact I].
    unfold so_id. unfold stdio_writev.
    assert (NE : so_buf so <> []) by (intros E; rewrite E in Lt; unfold zlength in Lt; cbn in Lt; lia).
    rewrite (iov_start_cons (so_buf so) [] NE).
    apply tok_wv_loop; [left; reflexivity| cbn; lia| |]; unfold WV_FUEL, iov_total; cbn [concat]; rewrite app_nil_r; lia.
  - cbn. exact I.
Qed.

Lemma naclient_outside : forall live frames (sp : Z) (W : list (Z * Z)) (a : Z),
  ~ aclient live frames sp a ->
  Forall (fun r => (sp <= fst r /\ snd r <= USTACK_TOP) \/ (forall x, fst r <= x < snd r -> client_static x)) W ->
  outside W a.
Proof.
  intros live frames sp W a NA H. induction H as [|[lo hi] W' Hr _ IH]; [exact I|]. cbn [outside fst snd] in *.
  split; [| exact IH]. intros Hx. apply NA. destruct Hr as [[H1 H2]|H3]; [left; lia| right; left; apply H3; exact Hx].
Qed.

Lemma file_cleanA : forall (m : mem) Fp flags wfn bufp bufsize fd mode lbf tail,
  rw_cells bsegs m Fp (file_cells flags 0 0 0 wfn bufp bufsize fd mode lbf tail) ->
  exists j0 j1 j2 j3, rw_cells bsegs m Fp (clean_file_cellsA j0 0 j1 0 j2 j3).
Proof.
  intros m Fp flags wfn bufp bufsize fd mode lbf tail H. unfold file_cells in H.
  pose proof (rw_cells_split_n bsegs m Fp _ 21%nat (Fp + 144) H eq_refl) as [H1 _]. cbv [firstn] in H1. clear H.
  merge_at H1 0%nat 2%nat. merge_at H1 3%nat 2%nat. merge_at H1 5%nat 1%nat. merge_at H1 7%nat 11%nat.
  eexists _, _, _, _. exact H1.
Qed.

Lemma stdin_cleanA : forall (m : mem), stdin_file m -> exists j0 j1 j2 j3, rw_cells bsegs m 0x184be0 (clean_file_cellsA j0 0 j1 0 j2 j3).
Proof.
  intros m (j0 & j1 & j2 & j3 & j4 & H).
  pose proof (rw_cells_split_n bsegs m 0x184be0 _ 9%nat (0x184be0 + 144) H eq_refl) as [H1 _]. cbv [firstn] in H1. clear H.
  exists j0, j1, j2, j3. exact H1.
Qed.

Definition xenv_x (m : mem) : Prop :=
  (exists (cdt thr sec : byte) (tm1 : word), rw_cells bsegs m 0x6de678 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
  /\ rw_cells bsegs m 0x6debe8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x184bd8 [C8 (Z_to_bv 64 0x184af0)]
  /\ rw_cells bsegs m 0x184db8 [C8 (Z_to_bv 64 0x184cd0)]
  /\ stdin_file m /\ rw_cells bsegs m 0x184cc8 [C8 (Z_to_bv 64 0x184be0)]
  /\ gds_at m 0x184df0 asan_gds
  /\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x1862c0 [C8 v])
  /\ rw_cells bsegs m 0x186310 [C1 (Z_to_bv 8 0)]
  /\ (exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : byte, rw_cells bsegs m 0x6bc240 [C1 o1] /\ rw_cells bsegs m 0x6bc241 [C1 o2] /\ rw_cells bsegs m 0x6bc242 [C1 o3]
      /\ rw_cells bsegs m 0x6bc243 [C1 o4] /\ rw_cells bsegs m 0x6bc244 [C1 o5] /\ rw_cells bsegs m 0x6bc245 [C1 o6] /\ rw_cells bsegs m 0x6bc246 [C1 o7]
      /\ rw_cells bsegs m 0x6bc247 [C1 o8] /\ rw_cells bsegs m 0x6bc248 [C1 o9] /\ rw_cells bsegs m 0x6bc249 [C1 o10] /\ rw_cells bsegs m 0x6bc24a [C1 o11])
  /\ ios_block m.

Lemma xenv_x_of : forall m, XENV_coreA m -> xenv_x m.
Proof.
  intros m (_ & _ & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & _ & IOB).
  unfold xenv_x. repeat (split; [assumption|]). assumption.
Qed.

Definition cstat (so : stdout_st) (g : word) (m : mem) : Prop :=
  xenv_x m /\ OUT_repA so m /\ ERR_repA m /\ ro_cells bsegs m 0x6de428 [C8 g] /\ locx3A m /\ tplocA m.

Definition XSP (x : Z) : Prop :=
  (0x6de678 <= x < 0x6de680) \/ (0x6debe8 <= x < 0x6debf8) \/ (0x184bd8 <= x < 0x184cd0) \/ (0x184db8 <= x < 0x184dc0) \/ (0x184dc0 <= x < 0x1862c8)
  \/ (0x186310 <= x < 0x186311) \/ (0x6bc240 <= x < 0x6bc24b) \/ (0x6bc488 <= x < 0x6bcc28).
Definition CSP (x : Z) : Prop :=
  XSP x
  \/ (0x184af0 <= x < 0x184bd8) \/ (0x184cd0 <= x < 0x184db8) \/ (0x6debf8 <= x < 0x6df448)
  \/ (0x6de428 <= x < 0x6de430)
  \/ (0x6bcf40 <= x < 0x6bcf48) \/ (0x6bd0d0 <= x < 0x6bd0d8) \/ (0x6bd0e0 <= x < 0x6bd0e8) \/ (0x6be3b8 <= x < 0x6be3c0).

Lemma CSP_static : forall x, CSP x -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold CSP, XSP in Hx. lia. Qed.

Local Ltac trw H AG := apply (rw_cells_agree_nw bsegs _ _ _ _ H); apply (agree_sub _ _ _ _ AG); intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; unfold CSP, XSP; lia.
Local Ltac tro H AG := apply (ro_cells_agree bsegs _ _ _ _ H); apply (agree_sub _ _ _ _ AG); intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; unfold CSP, XSP; lia.

Lemma xenv_x_agree : forall m m', xenv_x m -> agree_on XSP m m' -> xenv_x m'.
Proof.
  intros m m' (LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR & IOB) AG.
  split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; trw C AG|].
  split; [trw OFL AG|]. split; [trw SEU AG|]. split; [trw SOU AG|].
  split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; trw C AG|].
  split; [trw SINU AG|].
  split; [apply (gds_at_agree _ m m' _ GDS); apply (agree_sub _ _ _ _ AG); intros xa Hxa; rewrite asan_gds_length in Hxa; cbn in Hxa; unfold XSP; lia|].
  split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| trw C AG]|].
  split; [trw CPL AG|].
  split.
  { destruct ODR as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
    exists o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11.
    split; [trw C1 AG|]. split; [trw C2 AG|]. split; [trw C3 AG|]. split; [trw C4 AG|]. split; [trw C5 AG|].
    split; [trw C6 AG|]. split; [trw C7 AG|]. split; [trw C8 AG|]. split; [trw C9 AG|]. split; [trw C10 AG| trw C11 AG]. }
  unfold ios_block in *. apply (rw_cells_agree_nw bsegs _ _ _ _ IOB). apply (agree_sub _ _ _ _ AG). intros xa Hxa.
  rewrite ios_cells_size in Hxa. unfold IOS in Hxa. cbn in Hxa. unfold XSP. lia.
Qed.

Lemma cstat_agree : forall so g m m', cstat so g m -> agree_on CSP m m' -> cstat so g m'.
Proof.
  intros so g m m' (XX & OUT & ERR & CAN & LX3 & TPL) AG.
  split; [apply (xenv_x_agree m m' XX); apply (agree_sub _ _ _ _ AG); intros x Hx; left; exact Hx|].
  split; [apply (OUT_locA so m m' OUT); intros a Ha; apply AG; destruct Ha as (lo & hi & Hin & Hx); cbn in Hin; unfold CSP, XSP;
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia|].
  split; [apply (ERR_locA m m' ERR); intros a Ha; apply AG; destruct Ha as (lo & hi & Hin & Hx); cbn in Hin; unfold CSP, XSP;
          destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia|].
  split; [tro CAN AG|].
  split; [destruct LX3 as (L1 & L2 & L3); split; [trw L1 AG| split; [trw L2 AG| trw L3 AG]]|].
  unfold tplocA, TP_A in *. trw TPL AG.
Qed.

Definition Qfin (code : Z) : (unit * stdout_st) -> machine_state -> Prop :=
  fun _ ms' => ms_svc_pending ms' = Some (Z_to_bv 64 94) /\ areg ms' 10 = Z_to_bv 64 code.

Section XExit.
Variable RT : rt_sig.
Variable LIBv : option Z -> mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AF_XIT : forall Σ m, ART RT Σ m -> xit_rt m.
Hypothesis AF_IXIT : forall Σ m, ART RT Σ m -> ixit_rt (rt_sp0 RT Σ) m.
Hypothesis AF_XC : forall Σ m, ART RT Σ m -> xcells (rt_sp0 RT Σ) m.
Hypothesis AF_IOSX : forall Σ m, ART RT Σ m -> iosx_img_facts m.
Hypothesis LIBX : forall v m, LIBv v m -> libx v m.
Hypothesis VECX : forall PMc, vecx_stmt RT PMc.
Hypothesis IFW : forall sp0, ifwrite0_stmt (ixit2 sp0) (sp0 - STACK_WIN).
Hypothesis IFFI : forall sp0, ifflush_idle_stmt (ixit_rt sp0) (sp0 - STACK_WIN).
Hypothesis IWC : forall sp0, iwcrtomb_stmt (ixit2 sp0) (sp0 - STACK_WIN).
Hypothesis IFFS : forall sp0, ifflush_stdout_stmt (ixit_rt sp0) (sp0 - STACK_WIN) so_id so_set.
Hypothesis SX0 : stdio_exit0_stmt.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, GLOBALS_TOP, X_DEPTH, VECX_DEPTH, XPRE_DEPTH, HDXA in *; lia.

Local Ltac nacl Ha := apply (naclient_outside _ _ _ _ _ Ha);
  repeat (apply Forall_cons; [cbn [fst snd]; first [left; ul | right; intros xq Hxq; apply client_static_intro; unfold AEX, AEX_A0, XTPLOC in Hxq; lia] |]);
  apply Forall_nil.

Local Ltac trw_mu H MU := apply (rw_cells_agree_nw bsegs _ _ _ _ H); apply (agree_of_munch _ _ _ _ MU); intros xq Hxq;
  cbn [cells_size csize Nat.add foe_frame aex_tbl aex_args clean_file_cellsA length] in Hxq; unfold AEX, AEX_A0, AEF_INCB, XWI, XTPLOC in *; cbn [outside]; ul.
Local Ltac tro_mu H MU := apply (ro_cells_agree bsegs _ _ _ _ H); apply (agree_of_munch _ _ _ _ MU); intros xq Hxq;
  cbn [cells_size csize Nat.add] in Hxq; unfold AEX, AEX_A0, LIBC_NLX, XWI, XTPLOC in *; cbn [outside]; ul.

Lemma exit_tail_impl : forall (Σx : rts RT) (ra gp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (usp : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (p1 p2 : list byte) (f3 f4 f5 a3v a4v a5v : word) (j8 : list byte) (xs3 xs2 xs1 : word)
    (code : Z) (so : stdout_st) (g : word),
  ART RT Σx m -> mem_inv bsegs m ->
  stk bsegs m lo usp -> rt_sp0 RT Σx - STACK_WIN <= lo -> lo + HDXA <= usp -> usp + 80 <= USTACK_TOP ->
  rw_cells bsegs m usp (foe_frame j8 xs3 xs2 xs1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET)) -> 0 <= code < 256 ->
  rw_cells bsegs m AEX (aex_tbl 2 p1 p2 f3 f4 f5) -> rw_cells bsegs m AEX_A0 (aex_args a3v a4v a5v) ->
  cstat so g m ->
  impl bsegs (at_node bsegs) ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (epost (Qfin code))
       (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 (AEX + 4)) s1 a0 a1 (Z_to_bv 64 2) a3 a4 a5 a6 a7
                (Z_to_bv 64 AEX) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 FOE_BODY) fc None m (seg_rom bsegs)).
Proof.
  intros until g. intros ART0 MI ST LOW LOD UTOP FR CODE TBL TA CS.
  pose proof (af_sp0_range RT AF Σx m ART0) as SP0R. pose proof (af_sp0_win RT AF Σx m ART0) as SP0W.
  assert (U0 : 0 <= usp < 2^64) by (destruct ST as (S0 & S1 & _); ul).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; exact U0).
  pose proof CS as (XX & OUT & ERR & CAN & LX3 & TPL).
  destruct XX as ((cdt & thr & sec & tm1 & LIBC) & _).
  assert (NL : ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)]) by exact (libc_nl_of_libc m cdt thr sec tm1 LIBC).
  destruct (AF_IXIT Σx m ART0) as (_ & _ & _ & GF & _ & _ & _ & _ & _ & CIO & _).

  eapply impl_evt.
  { exact (exit_c2 ra gp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 usp F fc m lo p1 p2 f3 f4 f5 a3v a4v a5v
             U0 ST ltac:(ul) ltac:(ul) NL TBL TA GF CIO MI). }
  intros ms5 PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & TBL5 & TA5).
  assert (ART5 : ART RT Σx m5).
  { apply (af_frame RT AF Σx m m5 lo ART0 LOW); [| exact WM5]. intros a Ha. apply MU5. nacl Ha. }
  assert (AG5 : agree_on CSP m m5) by (apply (agree_of_munch _ _ _ _ MU5); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
  pose proof (cstat_agree so g m m5 CS AG5) as CS5. destruct CS5 as (XX5 & OUT5 & ERR5 & CAN5 & LX35 & TPL5).
  assert (FR5 : rw_cells bsegs m5 usp (foe_frame j8 xs3 xs2 xs1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET))) by trw_mu FR MU5.
  assert (NL5 : ro_cells bsegs m5 LIBC_NLX [C1 (Z_to_bv 8 0)]) by tro_mu NL MU5.
  pose proof XX5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOB5).

  pose proof (ios_exitA_proof (ixit2 (rt_sp0 RT Σx)) (rt_sp0 RT Σx - STACK_WIN) (IX2_frame _) (IFW _)
                (ifflush_idle_lift _ _ _ (xcells_CF (rt_sp0 RT Σx)) (IFFI _)) (IWC _) so_id so_set
                (ifflush_stdout_lift _ _ _ (xcells_CF (rt_sp0 RT Σx)) so_id so_set (IFFS _))) as IOSX.
  unfold ios_exitA_stmt in IOSX.
  assert (GS5 : ro_cells bsegs m5 0x180cb8 [C8 (Z_to_bv 64 0x6de428)]) by exact (proj1 (af_got_lib RT AF Σx m5 ART5)).
  specialize (IOSX lo (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 AEX_IOS)
                    b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 AEX) (Z_to_bv 64 X_IOSDTOR) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m5 so g).
  rewrite EU in IOSX.
  specialize (IOSX ST5 ltac:(ul) ltac:(ul) ltac:(ul) eq_refl IOB5 (AF_IOSX Σx m5 ART5) LX35 TPL5 OUT5 ERR5 (conj GS5 CAN5) (conj (AF_IXIT Σx m5 ART5) (AF_XC Σx m5 ART5)) MI5).
  unfold implM in IOSX. change X_IOSDTOR_A with X_IOSDTOR in IOSX. change IOS with AEX_IOS in IOSX.
  eapply impl_post_evt''; [exact IOSX|]. clear IOSX.
  intros [|[xr so']] ms6 H6; [apply evt_done; exact I|].
  cbn [epost fst snd] in H6 |- *. unfold ios_exitA_post in H6.
  destruct H6 as (v0 & v1 & v2 & va0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m6 & so'' & flags & eflags & mode1 & mode2 & tail & etail
                  & -> & MU6 & WM6 & MI6 & ST6 & SO'' & _ & OUTC & FL72 & ERRC & FL40 & TPL6 & SSP6 & IOB6 & IX6).
  rewrite EU in MU6, ST6.
  assert (ART6 : ART RT Σx m6).
  { apply (af_frame RT AF Σx m5 m6 lo ART5 LOW); [| exact WM6]. intros a Ha. apply MU6. nacl Ha. }
  destruct (AF_XIT Σx m6 ART6) as (FA & GF6 & GCX & (dso & DSO) & GX & UG1 & UG2 & RG & MUX & SHC & AI & CP & THR & RMS & COV & SC1 & SC2 & SC3).
  assert (AG6 : agree_on XSP m5 m6) by (apply (agree_of_munch _ _ _ _ MU6); intros x Hx; unfold XSP in Hx; unfold XWI, XTPLOC; cbn [outside]; ul).
  pose proof (xenv_x_agree m5 m6 XX5 AG6) as XX6.
  destruct XX6 as ((cdt6 & thr6 & sec6 & tm6 & LIBC6) & OFL6 & SEU6 & SOU6 & SIN6 & SINU6 & GDS6 & (flag & FLGNZ & FLG6) & CPL6 & ODR6 & _).
  destruct ODR6 as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & OC1 & OC2 & OC3 & OC4 & OC5 & OC6 & OC7 & OC8 & OC9 & OC10 & OC11).
  assert (FR6 : rw_cells bsegs m6 usp (foe_frame j8 xs3 xs2 xs1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET))) by trw_mu FR5 MU6.
  assert (NL6 : ro_cells bsegs m6 LIBC_NLX [C1 (Z_to_bv 8 0)]) by tro_mu NL5 MU6.
  assert (TBL6 : rw_cells bsegs m6 AEX (aex_tbl 1 p1 p2 f3 f4 f5)) by trw_mu TBL5 MU6.
  assert (TA6 : rw_cells bsegs m6 AEX_A0 (aex_args a3v a4v a5v)) by trw_mu TA5 MU6.

  eapply evt_cut.
  { exact (exit_post gp v0 v1 v2 (Z_to_bv 64 AEX_IOS) va0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 X_IOSDTOR) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 usp F fc m6 lo
             p1 p2 f3 f4 f5 a3v a4v a5v j8 xs3 xs2 xs1 (Z_to_bv 64 code) o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 flag dso
             ltac:(lia) ltac:(ul) ST6 ltac:(ul) ltac:(ul) FR6 NL6 TBL6 TA6 COV FA GF6 GCX DSO GX CPL6 FLG6 FLGNZ (conj UG1 UG2) RG MUX SHC AI CP THR RMS
             SC1 SC2 SC3 GDS6 OC1 OC2 OC3 OC4 OC5 OC6 OC7 OC8 OC9 OC10 OC11 MI6). }
  intros ms7 PO7. destruct PO7 as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m7 & -> & MU7 & WM7 & MI7 & ST7).

  assert (LIBC7 : rw_cells bsegs m7 0x6de678 [C1 cdt6; C1 thr6; C1 sec6; C1 (Z_to_bv 8 0); C4 tm6]) by trw_mu LIBC6 MU7.
  assert (OFL7 : rw_cells bsegs m7 0x6debe8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by trw_mu OFL6 MU7.
  assert (SINU7 : rw_cells bsegs m7 0x184cc8 [C8 (Z_to_bv 64 0x184be0)]) by trw_mu SINU6 MU7.
  assert (SOU7 : rw_cells bsegs m7 0x184db8 [C8 (Z_to_bv 64 0x184cd0)]) by trw_mu SOU6 MU7.
  assert (SEU7 : rw_cells bsegs m7 0x184bd8 [C8 (Z_to_bv 64 0x184af0)]) by trw_mu SEU6 MU7.
  destruct (stdin_cleanA m6 SIN6) as (i0 & i1 & i2 & i3 & SINC).
  destruct (file_cleanA m6 _ _ _ _ _ _ _ _ _ OUTC) as (q0 & q1 & q2 & q3 & SOUC).
  destruct (file_cleanA m6 _ _ _ _ _ _ _ _ _ ERRC) as (e0 & e1 & e2 & e3 & SERC).
  assert (SINC7 : rw_cells bsegs m7 0x184be0 (clean_file_cellsA i0 0 i1 0 i2 i3)) by trw_mu SINC MU7.
  assert (SOUC7 : rw_cells bsegs m7 0x184cd0 (clean_file_cellsA q0 0 q1 0 q2 q3)) by trw_mu SOUC MU7.
  assert (SERC7 : rw_cells bsegs m7 0x184af0 (clean_file_cellsA e0 0 e1 0 e2 e3)) by trw_mu SERC MU7.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + 48)) = usp + 48) by (apply unsigned_lit; ul).
  pose proof (SX0 (Z_to_bv 64 0x1607c4) (Z_to_bv 64 (usp + 48)) gp (Z_to_bv 64 TP_A) w0 w1 w2 (Z_to_bv 64 code) xs1 d0 d1 d2 d3 d4 d5 d6 d7 xs2 xs3
                s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F fc m7 lo i0 i1 i2 i3 q0 q1 q2 q3 e0 e1 e2 e3 0 0 0 0 0 0 cdt6 thr6 sec6 tm6) as SX.
  rewrite EU48 in SX.
  specialize (SX ST7 ltac:(ul) ltac:(ul) LIBC7 OFL7 SINU7 SINC7 SOU7 SOUC7 SEU7 SERC7
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MI7).
  eapply evt_cut; [exact SX|]. clear SX.
  intros ms8 PO8. destruct PO8 as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m8 & -> & MU8 & WM8 & MI8 & ST8).

  rewrite (ret_pc_even 0x1607c4) by lia.
  eapply evt_mono; [exact (exit_tail_spec (usp + 48) code gp (Z_to_bv 64 TP_A) x0 x1 x2 xs1 y0 y1 y2 y3 y4 y5 y6 y7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11
                             x3 x4 x5 x6 F fc m8 ltac:(lia) MI8)|].
  intros ms9 (ra9 & ->). cbn [epost Qfin]. split; reflexivity.
Qed.

Definition after_vec (Σ : rts RT) (PMc : Model -> Prop) (usp lo : Z) (A8 : Z) (m : mem)
    (gp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (c2 : config) : Prop :=
  exists (Σ' : rts RT) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
    ASTA RT Σ' PMc (eq (MS (mkR (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 AEX_VEC_OBJ)
                                   a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 AEX) (Z_to_bv 64 X_VECDTOR) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                              F' (ret_pc (Z_to_bv 64 AEX_HRA)) fc None m' (seg_rom bsegs))) c2
    /\ rt_after_f RT Σ' (usp + -64) lo m m'
    /\ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ) (usp + -64) VECX_W m m'
    /\ rt_sp0 RT Σ' = rt_sp0 RT Σ.

Theorem exit_ok : exit_contract_imp RT XENV_coreA OUT_repA ERR_repA LIBv.
Proof.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m so code lo v
    Ha0 Hcode Htp Hso HFD OUT ERR XE AEXX LIB LIVE ART0 MI0 CALL SLACK SSP.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP in Hc. subst a0 tp.
  unfold entry_st, e_exit in Hc.
  assert (SOK : (so_first so = false \/ so_buf so = []) /\ zlength (so_buf so) <= 2^26).
  { destruct Hso as [->|(k & Hk5 & ->)].
    - split; [right; reflexivity| unfold zlength; cbn; lia].
    - split; [left; reflexivity|]. cbn [so_lines so_buf]. rewrite zlength_zeros_out. lia. }

  assert (FIN : forall (Σx : rts RT) (cx : config) (msx : machine_state),
            ASTA RT Σx (PMfd F0 fs0) (eq msx) cx ->
            impl bsegs (at_node bsegs) ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (epost (Qfin code)) msx ->
            realizes bsegs cx (t_emit (evw 1 (so_buf so)) T)).
  { intros Σx cx msx Hcx IMPL.
    assert (RZ : realizes bsegs cx (TT ((stdout_exit_flush so_id so_set : @M stdout_st unit) so) (fun _ => t_emit [] T))).
    { apply (impl_realizes bsegs SEGTOP_A asegs_wx asegs_below [1] _ (rt_allow RT Σx) (fun mo => ARTM RT Σx mo /\ PMfd F0 fs0 mo) (Qfin code)
               (fun _ => t_emit [] T) msx cx (ASTA_PM_mat_stable RT AF Σx F0 fs0)); [| exact (tok_exit_flush so (proj1 SOK) (proj2 SOK))| exact Hcx| exact IMPL|].
      - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
      - intros x ms' c' (HS & HA0) Hc'.
        assert (R : realizes bsegs c' T).
        { apply Hk. exists (rt_allow RT Σx), (eq ms'), (fun mo => ARTM RT Σx mo /\ PMfd F0 fs0 mo). split; [exact Hc'|]. split.
          + intros ms <-. split; [right; exact HS| exact HA0].
          + intros mo (_ & _ & HFS). exact HFS. }
        eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty bsegs _ _ R). }
    eapply rz_conseq; [exact RZ|].
    eapply t_eq_trans; [apply TT_exit_flush; [exact (proj1 SOK)| exact (proj2 SOK)| apply t_emit_has_nil]|].
    eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl. }

  pose proof (xenv_x_of m XE) as XX.
  destruct XE as ((tid & HT & TID) & EXL & (cdt & thr & sec & tm1 & LIBC) & _).
  assert (NL : ro_cells bsegs m LIBC_NLX [C1 (Z_to_bv 8 0)]) by exact (libc_nl_of_libc m cdt thr sec tm1 LIBC).
  destruct (AF_IXIT Σ m ART0) as (_ & _ & _ & GF & _ & _ & _ & _ & _ & CIO & _).
  destruct SSP as (g & _ & CAN).
  destruct (LIBX _ _ LIB) as (LX3 & TPL & LV).
  assert (CS0 : cstat so g m) by (split; [exact XX| split; [exact OUT| split; [exact ERR| split; [exact CAN| split; [exact LX3| exact TPL]]]]]).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  destruct v as [A8|].
  -
    destruct LV as [VW A16]. cbn [aexX] in AEXX. destruct AEXX as ((p1 & p2 & TBL) & TA & LATCH & INCB).
    specialize (LIVE A8 eq_refl).

    pose proof (exit_pre6 ra gp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 usp F fc m lo tid p1 p2
                  ltac:(lia) ltac:(ul) ST ltac:(ul) ltac:(ul) TID HT EXL NL TBL TA GF CIO MI0) as W1.
    lazymatch type of W1 with evt bsegs _ ?X => assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end. clear W1.
    apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1. clear W1'.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & PO1 & Hc1'). clear Hc1.
    destruct PO1 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & j8 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FRX1 & FRF1 & EXL1 & TBL1 & TA1).
    assert (ART1 : ART RT Σ m1).
    { apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. nacl Ha. }
    assert (AG1 : agree_on CSP m m1) by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
    pose proof (cstat_agree so g m m1 CS0 AG1) as CS1.
    assert (VW1 : rw_cells bsegs m1 AEX_VEC_OBJ [C8 (Z_to_bv 64 A8); C8 (Z_to_bv 64 (A8 + 8)); C8 (Z_to_bv 64 (A8 + 8))]).
    { apply (rw_cells_agree_nw bsegs _ _ _ _ VW). apply (agree_of_munch _ _ _ _ MU1). intros xq Hxq.
      cbn [cells_size csize Nat.add] in Hxq. unfold AEX, AEX_VEC_OBJ in *. cbn [outside]. ul. }
    assert (INCB1 : rw_cells bsegs m1 AEF_INCB [C1 (Z_to_bv 8 0)]) by trw_mu INCB MU1.

    assert (EU64 : bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64) by (apply unsigned_lit; ul).
    assert (CALL1 : call_ok RT Σ m1 (Z_to_bv 64 (usp + -64)) lo).
    { unfold call_ok. rewrite EU64. split; [exact ST1|]. split; [exact LOW|]. split; [ul|]. split; [ul|].
      replace (usp + -64) with (usp - 64) by lia. rewrite Zminus_mod, SPA. reflexivity. }
    assert (S0B : bv_unsigned (Z_to_bv 64 (AEX + 4)) <= bv_unsigned (Z_to_bv 64 (usp + -64)) - 16).
    { rewrite EU64. unfold AEX. rewrite unsigned_lit by lia. ul. }
    assert (RAB : 0 <= bv_unsigned (Z_to_bv 64 AEX_HRA) < 2^64) by (unfold AEX_HRA; rewrite unsigned_lit by lia; lia).
    pose proof (VECX (PMfd F0 fs0) Σ (after_vec Σ (PMfd F0 fs0) usp lo A8 m1 gp s4 s5 s6 s7 s8 s9 s10 s11 F fc)
                (Z_to_bv 64 AEX_HRA) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 (AEX + 4)) (Z_to_bv 64 AEX_VEC_OBJ)
                (Z_to_bv 64 AEX_VEC_OBJ) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 AEX) (Z_to_bv 64 X_VECDTOR) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 A8 lo
                (PMfd_fdfs_only F0 fs0) (PMfd_mat_stable F0 fs0) eq_refl eq_refl LIVE A16 VW1 ART1 MI1 CALL1 ltac:(rewrite EU64; ul) S0B RAB) as VX.
    lazymatch type of VX with ?KH -> _ => assert (KHP : KH) end.
    { intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' RA PRES VW' LVE FRS SP0 CRD.
      unfold kcont, cps. intros T' c' H' K'. apply K'. unfold after_vec. rewrite EU64 in RA, PRES.
      exists Σ', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', m'.
      split; [exact H'| split; [exact RA| split; [exact PRES| exact SP0]]]. }
    apply (cps_realizes bsegs _ _ _ c1 (VX KHP) Hc1'). clear VX KHP.
    intros c2 AV. clear Hc1'. unfold after_vec, rt_after_f in AV.
    destruct AV as (Σ' & v0 & v1 & v2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & F' & m2 & Hc2 & (ART2 & MI2 & ST2) & PRES2 & SP2).
    assert (AG2 : agree_on CSP m1 m2).
    { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx. split; [right; left; exact (CSP_static x Hx)|].
      unfold VECX_W, AEX_VEC_OBJ. unfold CSP, XSP in Hx. cbn [outside]. lia. }
    pose proof (cstat_agree so g m1 m2 CS1 AG2) as CS2.

    assert (AGS : agree_on (fun x => (usp - 64 <= x < usp) \/ (AEX <= x < AEX + 80) \/ (AEX_A0 <= x < AEX_A0 + 48) \/ (x = AEF_INCB) \/ (0x6de678 <= x < 0x6de680)) m1 m2).
    { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2). intros x Hx. unfold VECX_W, AEX, AEX_A0, AEF_INCB, AEX_VEC_OBJ in *. cbn [outside]. split; [| ul].
      destruct Hx as [Hx|Hx]; [left; ul| right; left; apply client_static_intro; lia]. }
    Local Ltac tr2 H AGS := first [apply (rw_cells_agree_nw bsegs _ _ _ _ H) | apply (ro_cells_agree bsegs _ _ _ _ H)]; apply (agree_sub _ _ _ _ AGS); intros xq Hxq;
      cbn [cells_size csize Nat.add foe_frame aex_tbl aex_args length] in Hxq; unfold AEX, AEX_A0, AEF_INCB, LIBC_NLX in *; lia.
    assert (FRF2 : rw_cells bsegs m2 (usp + -64) (foe_frame j8 s3 s2 s1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET))) by tr2 FRF1 AGS.
    assert (NL1 : ro_cells bsegs m1 LIBC_NLX [C1 (Z_to_bv 8 0)]) by tro_mu NL MU1.
    assert (NL2 : ro_cells bsegs m2 LIBC_NLX [C1 (Z_to_bv 8 0)]) by tr2 NL1 AGS.
    assert (TBL2 : rw_cells bsegs m2 AEX (aex_tbl 4 p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 X_VECDTOR) (Z_to_bv 64 X_ATCXA))) by tr2 TBL1 AGS.
    assert (TA2 : rw_cells bsegs m2 AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0))) by tr2 TA1 AGS.
    assert (INCB2 : rw_cells bsegs m2 AEF_INCB [C1 (Z_to_bv 8 0)]) by tr2 INCB1 AGS.

    apply (FIN Σ' c2 _ Hc2).
    eapply impl_evt.
    { exact (exit_r4 gp v0 v1 v2 (Z_to_bv 64 AEX_VEC_OBJ) w0 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 X_VECDTOR) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (usp + -64) F' fc m2
               p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 X_VECDTOR) (Z_to_bv 64 X_ATCXA) ltac:(ul) NL2 TBL2 MI2). }
    intros ms3 PO3. destruct PO3 as (ra3 & x0 & x1 & x3 & m3 & -> & MU3 & WM3 & MI3 & TBL3).
    assert (ART3 : ART RT Σ' m3).
    { apply (af_frame RT AF Σ' m2 m3 lo ART2 ltac:(rewrite SP2; exact LOW)); [| exact WM3]. intros a Ha. apply MU3. nacl Ha. }
    assert (AG3 : agree_on CSP m2 m3) by (apply (agree_of_munch _ _ _ _ MU3); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
    pose proof (cstat_agree so g m2 m3 CS2 AG3) as CS3.
    assert (FRF3 : rw_cells bsegs m3 (usp + -64) (foe_frame j8 s3 s2 s1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET))) by trw_mu FRF2 MU3.
    assert (NL3 : ro_cells bsegs m3 LIBC_NLX [C1 (Z_to_bv 8 0)]) by tro_mu NL2 MU3.
    assert (TA3 : rw_cells bsegs m3 AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0))) by trw_mu TA2 MU3.
    assert (INCB3 : rw_cells bsegs m3 AEF_INCB [C1 (Z_to_bv 8 0)]) by trw_mu INCB2 MU3.
    assert (ST3 : stk bsegs m3 lo (usp + -64)).
    { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. unfold AEX. cbn [outside]. ul. }

    eapply impl_evt.
    { exact (exit_c3 ra3 gp v0 v1 v2 (Z_to_bv 64 AEX_VEC_OBJ) x0 x1 x3 w4 w5 w6 w7 (Z_to_bv 64 X_VECDTOR) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (usp + -64) F' fc m3
               p1 p2 (Z_to_bv 64 X_VECDTOR) (Z_to_bv 64 X_ATCXA) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0) ltac:(ul) NL3 TBL3 TA3 INCB3 MI3). }
    intros ms4 PO4. destruct PO4 as (ra4 & y0 & y1 & y2 & ys1 & ya0 & ya1 & ya3 & ys3 & m4 & -> & MU4 & WM4 & MI4 & TBL4).
    assert (ART4 : ART RT Σ' m4).
    { apply (af_frame RT AF Σ' m3 m4 lo ART3 ltac:(rewrite SP2; exact LOW)); [| exact WM4]. intros a Ha. apply MU4. nacl Ha. }
    assert (AG4 : agree_on CSP m3 m4) by (apply (agree_of_munch _ _ _ _ MU4); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
    pose proof (cstat_agree so g m3 m4 CS3 AG4) as CS4.
    assert (FRF4 : rw_cells bsegs m4 (usp + -64) (foe_frame j8 s3 s2 s1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET))) by trw_mu FRF3 MU4.
    assert (TA4 : rw_cells bsegs m4 AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0))) by trw_mu TA3 MU4.
    assert (ST4 : stk bsegs m4 lo (usp + -64)).
    { apply (stk_agree bsegs m3 m4 _ _ ST3); [| exact WM4]. apply (agree_of_munch _ _ _ _ MU4). intros x Hx. unfold AEX. cbn [outside]. ul. }

    exact (exit_tail_impl Σ' ra4 gp y0 y1 y2 ys1 ya0 ya1 ya3 w4 w5 w6 w7 ys3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 (usp + -64) F' fc m4 lo
             p1 p2 (Z_to_bv 64 X_CALL) (Z_to_bv 64 X_VECDTOR) (Z_to_bv 64 X_ATCXA) (Z_to_bv 64 X_AEXGUARD) (Z_to_bv 64 AEX_VEC_OBJ) (Z_to_bv 64 0) j8 s3 s2 s1 code so g
             ART4 MI4 ST4 ltac:(rewrite SP2; exact LOW) ltac:(ul) ltac:(ul) FRF4 Hcode TBL4 TA4 CS4).
  -
    cbn [aexX] in AEXX. clear LIVE LV VECX. apply (FIN Σ c _ Hc). destruct AEXX as [MAIN|REG].
    + destruct MAIN as ((p1 & p2 & f3 & f4 & f5 & TBL) & (a3v & a4v & a5v & TA) & LATCH & INCB).
      eapply impl_evt.
      { exact (exit_head3 ra gp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 usp F fc m lo tid p1 p2 f3 f4 f5 a3v a4v a5v
                 ltac:(lia) ltac:(ul) ST ltac:(ul) ltac:(ul) TID HT EXL NL TBL TA MI0). }
      intros ms1 PO1. destruct PO1 as (ra1 & u0 & u1 & u2 & ua0 & ua1 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & j8 & m1 & -> & MU1 & WM1 & MI1 & ST1
                                       & FRX1 & FRF1 & EXL1 & TBL1 & TA1).
      assert (ART1 : ART RT Σ m1).
      { apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. nacl Ha. }
      assert (AG1 : agree_on CSP m m1) by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
      pose proof (cstat_agree so g m m1 CS0 AG1) as CS1.
      exact (exit_tail_impl Σ ra1 gp u0 u1 u2 s1 ua0 ua1 ua3 ua4 ua5 ua6 ua7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (usp + -64) F fc m1 lo
               p1 p2 f3 f4 f5 a3v a4v a5v j8 s3 s2 s1 code so g ART1 MI1 ST1 LOW ltac:(ul) ltac:(ul) FRF1 Hcode TBL1 TA1 CS1).
    + destruct REG as ((p1 & p2 & f4 & f5 & TBL) & (a4v & a5v & TA) & LATCH & INCB).
      eapply impl_evt.
      { exact (exit_head4 ra gp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 usp F fc m lo tid p1 p2 f4 f5 a4v a5v
                 ltac:(lia) ltac:(ul) ST ltac:(ul) ltac:(ul) TID HT EXL NL TBL TA MI0). }
      intros ms1 PO1. destruct PO1 as (ra1 & u0 & u1 & u2 & ua0 & ua1 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & j8 & m1 & -> & MU1 & WM1 & MI1 & ST1
                                       & FRX1 & FRF1 & EXL1 & TBL1 & TA1).
      assert (ART1 : ART RT Σ m1).
      { apply (af_frame RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. nacl Ha. }
      assert (AG1 : agree_on CSP m m1) by (apply (agree_of_munch _ _ _ _ MU1); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
      pose proof (cstat_agree so g m m1 CS0 AG1) as CS1.
      assert (NL1 : ro_cells bsegs m1 LIBC_NLX [C1 (Z_to_bv 8 0)]) by tro_mu NL MU1.
      assert (INCB1 : rw_cells bsegs m1 AEF_INCB [C1 (Z_to_bv 8 0)]) by trw_mu INCB MU1.

      eapply impl_evt.
      { exact (exit_c3 ra1 gp u0 u1 u2 s1 ua0 ua1 ua3 ua4 ua5 ua6 ua7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (usp + -64) F fc m1
                 p1 p2 f4 f5 a4v a5v ltac:(ul) NL1 TBL1 TA1 INCB1 MI1). }
      intros ms2 PO2. destruct PO2 as (ra2 & y0 & y1 & y2 & ys1 & ya0 & ya1 & ya3 & ys3 & m2 & -> & MU2 & WM2 & MI2 & TBL2).
      assert (ART2 : ART RT Σ m2).
      { apply (af_frame RT AF Σ m1 m2 lo ART1 LOW); [| exact WM2]. intros a Ha. apply MU2. nacl Ha. }
      assert (AG2 : agree_on CSP m1 m2) by (apply (agree_of_munch _ _ _ _ MU2); intros x Hx; unfold CSP, XSP in Hx; unfold AEX; cbn [outside]; ul).
      pose proof (cstat_agree so g m1 m2 CS1 AG2) as CS2.
      assert (FRF2 : rw_cells bsegs m2 (usp + -64) (foe_frame j8 s3 s2 s1 (Z_to_bv 64 code) (Z_to_bv 64 X_EXIT_FOE_RET))) by trw_mu FRF1 MU2.
      assert (TA2 : rw_cells bsegs m2 AEX_A0 (aex_args (Z_to_bv 64 X_AEXGUARD) a4v a5v)) by trw_mu TA1 MU2.
      assert (ST2 : stk bsegs m2 lo (usp + -64)).
      { apply (stk_agree bsegs m1 m2 _ _ ST1); [| exact WM2]. apply (agree_of_munch _ _ _ _ MU2). intros x Hx. unfold AEX. cbn [outside]. ul. }
      exact (exit_tail_impl Σ ra2 gp y0 y1 y2 ys1 ya0 ya1 ya3 ua4 ua5 ua6 ua7 ys3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (usp + -64) F fc m2 lo
               p1 p2 (Z_to_bv 64 X_CALL) f4 f5 (Z_to_bv 64 X_AEXGUARD) a4v a5v j8 s3 s2 s1 code so g ART2 MI2 ST2 LOW ltac:(ul) ltac:(ul) FRF2 Hcode TBL2 TA2 CS2).
Qed.

End XExit.
