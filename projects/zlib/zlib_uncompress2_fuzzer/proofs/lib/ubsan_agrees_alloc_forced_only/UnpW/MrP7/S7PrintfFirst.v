(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import WsegFast PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim ShapeAlg Nodes AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux RefMemcpyLib RefNodes Hoare. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S7ExitBase S7StdioDefs S7StdioWrite S7LibStdioCall. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RefPrintfLib.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require S7PrintfBufBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Spec.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP7 Require Import S7SoDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rz_run_lf : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') -> log_flat E (s_log ss') ->
     realizes segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  realizes segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [| reflexivity | exact Hlf].
  eapply carry_after; eassumption.
Qed.

(* [comment removed for export] *)
Theorem stdio_call_sound_post {RCa1 : RunCtx}  :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 2 ^ 64)%Z ->
  (wp <= TASK_SIZE)%Z ->
  (bv_unsigned s + bv_unsigned l <= TASK_SIZE)%Z ->
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model) K) ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst R (Z_to_bv 64 0x1b5d4) M (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) 0x21c48 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread (run_segments RSEGS rc_inp rc_sp rc_mb) kn (ELit 0) 0x93228 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hlenp Hlene H30 Dw Ds Hsl Tsp Tsl Rpend Rextra Hfdlk Hrdr Hh Hlz HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) 0x21c48 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn (run_segments RSEGS rc_inp rc_sp rc_mb) E M kn (ELit 0) 0x93228 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x1b5d4) with (0x1b5d4%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact Hh.
  - exact Hlz.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Tsp.
  - exact Tsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT.
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite S7LibStdioCall.u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite S7LibStdioCall.u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
    + exact HPOST.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pf1_vals (regs : bvmap 5 word) (sp : word) (can : Z) : list word :=
  [sp; Z_to_bv 64 can] ++ junk_vals regs.

Definition pf1E (regs : bvmap 5 word) (sp : word) (can : Z) : env :=
  Env (vals_ev (pf1_vals regs sp can)) (blobs_ev []).

Definition pf1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x14c78 | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

Definition pf1_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) (4294967296 + 1200) 0x7fffffffffff;
   KWr (SA (EVar 0) (-1200)) 1200;
   KImg 0x10000 0x21c48; KImg 0x21c50 0x22000; KImg 0x22d78 0x22e60; KImg 0x93688 0x93a90;
   KWord (SA (ELit 0) 0x21c48) 8 (ELit 0x93228);
   KWord (SA (ELit 0) 0x93228) 8 (EVar 1);
   KWr (SA (ELit 0) 0x22000) 0x72000].

Definition PF1_FUEL : nat := 3000.
Definition pf1_scr : scripts := SCR [] [] [].

(* [comment removed for export] *)
Definition pf1_regions : list sregion :=
  [(SA (EVar 0) (-1200), 1200); (SA (ELit 0) 0x22d78, 232); (SA (ELit 0) 0x93688, 1032)].

Lemma pf1_vals_length : forall regs sp can, length (pf1_vals regs sp can) = 34%nat.
Proof. intros. unfold pf1_vals. rewrite length_app, junk_vals_length. reflexivity. Qed.

Section Entry.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z).
  Hypothesis PP : pf_pre mem sp can.
  Hypothesis SO : so_pristine mem.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x14c78.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pf1E regs sp can.

  Lemma pf1_ev_junk : forall i, (2 <= i < 34)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros i Hi. unfold E, pf1E, pf1_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 can] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma pf1_ev0 : ev E 0 = sp. Proof. reflexivity. Qed.
  Lemma pf1_ev1 : ev E 1 = Z_to_bv 64 can. Proof. reflexivity. Qed.

  Lemma pf1_regs_ok : regs_ok E pf1_sr regs.
  Proof.
    apply S7PrintfBufBase.regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth pf1_sr S7PrintfBufBase.allregs32 edenot].
    1: apply getr_zero.
    1: exact R1.
    1: exact R2.
    9: exact R11.
    all: rewrite pf1_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  Lemma pf1_know_ok : know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem pf1_kn.
  Proof.
    destruct PP as [P16 Plo Phi Pstk Pimg Pgot Pcan Pcan64]. unfold PF1_FR in *. pose proof (u64_range sp) as Hsp.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    unfold pf1_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite pf1_ev0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite pf1_ev0. lia.
    - apply (kwr_of_stk_ok (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (EVar 0) sp 1200); [apply pf1_ev0 | exact Pstk | lia].
    - apply kimg_intro; [lia | lia | intros i Hi; apply Pimg; lia].
    - apply kimg_intro; [lia | lia | intros i Hi; apply Pimg; lia].
    - apply kimg_intro; [lia | lia | intros i Hi; apply SO; left; lia].
    - apply kimg_intro; [lia | lia | intros i Hi; apply SO; right; lia].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pgot].
    - eapply (kword_intro (run_segments RSEGS rc_inp rc_sp rc_mb) E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | apply pf1_ev1 | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact Pcan].
    - cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite Z0.
      split; [lia|]. intros d m Hd Hm. apply store_ok_data; rewrite u64_lit by lia; lia.
  Qed.
End Entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pf1_regions_denot : forall (E : env) (sp : word), ev E 0 = sp -> map (rdenot E) pf1_regions = so_regions sp.
Proof.
  intros E sp H. unfold pf1_regions, so_regions, rdenot, estart, PF1_FR. cbn [map fst snd a_base a_off edenot]. rewrite H.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. replace (bv_unsigned sp + -1200) with (bv_unsigned sp - 1200) by lia. reflexivity.
Qed.

Lemma pf1_regions_flat : forall (E : env) (sp : word),
  ev E 0 = sp -> 4294967296 + 1200 <= bv_unsigned sp -> regions_flat E pf1_regions.
Proof.
  intros E sp H Hlo r Hr. pose proof (u64_range sp) as Hsp. unfold pf1_regions in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; unfold flat, estart; cbn [fst snd a_base a_off edenot]; rewrite ?H;
    change (bv_unsigned (Z_to_bv 64 0)) with 0; lia.
Qed.

(* [comment removed for export] *)
Lemma pf1_block_frame : forall (E : env) (sp : word) base log,
  ev E 0 = sp -> 4294967296 + 1200 <= bv_unsigned sp ->
  log_covered pf1_regions log = true -> log_flat E log ->
  frame_mod base (mem_denot E base log) (so_regions sp).
Proof.
  intros E sp base log H Hlo Hc Hlf. rewrite <- (pf1_regions_denot E sp H).
  apply log_covered_frame; [exact Hc | apply (pf1_regions_flat E sp H Hlo) | exact Hlf].
Qed.

(* [comment removed for export] *)
Lemma pf1_sw_frame {RCa1 : RunCtx}  : forall (sp : word) M M' bufp bufsz,
  4294967296 + 1200 <= bv_unsigned sp ->
  sw_post M (bv_unsigned sp - 1088) 0x22d78 bufp bufsz M' -> frame_mod M M' (so_regions sp).
Proof.
  intros sp M M' bufp bufsz Hlo [Pagree Pgrows _ _ _]. pose proof (u64_range sp) as Hsp.
  split; [|exact Pgrows]. intros a Ho. unfold so_regions, PF1_FR in Ho. cbn [outside] in Ho. unfold in_rng in Ho.
  rewrite !u64_lit in Ho by lia. apply Pagree; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac run_block_lf HR HK fuel stops scr NX :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- realizes _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (rz_run_lf segs fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M rom R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | split_foralls
            | split_foralls
            | try reflexivity; try assumption
            | try reflexivity; try assumption
            | ]
          end
        end
      end
    end
  end.

Theorem printf0_first {RCa1 : RunCtx}  : printf0_first_stmt.
Proof.
  intros regs mem model sp can K PP SO R1 R2 R11 Hfd Hrdr Hh Hl HKnil HCONT.
  pose proof PP as [P16 Plo Phi _ _ _ _ Pcan64]. unfold PF1_FR in Plo. pose proof (u64_range sp) as Hsp.
  pose proof (pf1_regs_ok regs sp can R1 R2 R11) as HR.
  pose proof (pf1_know_ok regs mem sp can PP SO) as HK.
  unfold pf1E in HR, HK. set (vals := pf1_vals regs sp can) in *.
  assert (HL : length vals = 34%nat) by apply pf1_vals_length.
  assert (P0 : vals_ev vals 0 = sp) by reflexivity.
  pose proof HR as HR0.
  (* [comment removed for export] *)
  run_block_lf HR HK PF1_FUEL (@nil Z) pf1_scr 34%nat.
  clear HR HK. intros Ra Ma HR HK EQa LFa. cbn [s_pc s_regs s_log] in HR, EQa, LFa |- *.
  assert (FMa : frame_mod mem Ma (so_regions sp)).
  { rewrite EQa. apply pf1_block_frame; [exact P0 | exact Plo | vm_compute; reflexivity | exact LFa]. }
  clear EQa LFa.
  (* [comment removed for export] *)
  assert (HF : fetch_word (run_segments RSEGS rc_inp rc_sp rc_mb) (Z_to_bv 64 0x1b7c8) = Some ECALLW) by (vm_compute; reflexivity).
  eapply (rz_ioctl_winsz (run_segments RSEGS rc_inp rc_sp rc_mb) _ _ _ model ECALLW (Z_to_bv 64 1) (Z_to_bv 64 1));
    [ exact HF | apply is_ecall_ECALLW | exact Hh | exact Hl
    | regv HR (17%bv : reg); reflexivity
    | regv HR (10%bv : reg); reflexivity
    | rewrite u64_lit by lia; lia
    | exact Hfd
    | regv HR (11%bv : reg); reflexivity
    | ].
  rewrite (v_addi_pc4 0x1b7c8) by lia. change (0x1b7c8 + 4) with 0x1b7cc.
  assert (HR' := regs_set_a0 _ _ _ (errno_ret ENOTTY) (ELit (two64 - 25)) HR
                   ltac:(cbn [edenot]; unfold errno_ret, ENOTTY; apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; reflexivity)).
  clear HR. rename HR' into HR.
  (* [comment removed for export] *)
  run_block_lf HR HK PF1_FUEL [0x1b5d4] pf1_scr 34%nat.
  clear HR HK. intros Rb Mb HR HK EQb LFb. cbn [s_pc s_regs s_log] in HR, EQb, LFb |- *.
  assert (FMb : frame_mod Ma Mb (so_regions sp)).
  { rewrite EQb. apply pf1_block_frame; [exact P0 | exact Plo | vm_compute; reflexivity | exact LFb]. }
  clear EQb LFb.
  (* [comment removed for export] *)
  lazymatch type of HR with regs_ok _ ?sr _ => lazymatch type of HK with know_ok _ _ _ ?kn =>
    let sc := eval vm_compute in (stdio_call 34 sr kn) in
    lazymatch sc with
    | Some ?res =>
        assert (SC : stdio_call (length vals) sr kn = Some res) by (rewrite HL; vm_cast_no_check (@eq_refl _ (Some res)));
        apply (stdio_call_sound_post vals (blobs_ev []) sr kn Rb Mb model res [Z_to_bv 8 0x30] [Z_to_bv 8 0x0a] K HR HK SC);
        cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn]
    end end end.
  all: try (rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off]).
  all: cbn [edenot ev length Z.of_nat Pos.of_succ_nat Pos.succ app].
  all: rewrite ?P0.
  all: try (rewrite !u64_lit by lia).
  1-4: cbn; lia.
  1-2: left; lia.
  1: lia.
  1-2: unfold TASK_SIZE; lia.
  1: { let H := fresh "Hb" in krd HK 603792 1%nat H; exact H. }
  1: { let H := fresh "Hb" in krd HK 66358 1%nat H; exact H. }
  1: exact Hfd.
  1: exact Hrdr.
  1: exact Hh.
  1: exact Hl.
  1: exact HKnil.
  (* [comment removed for export] *)
  clear HR HK SC. intros Rc Mc HR HK POST.
  assert (FMc : frame_mod Mb Mc (so_regions sp)).
  { eapply pf1_sw_frame; [exact Plo|]. replace (bv_unsigned sp - 1088) with (bv_unsigned sp + -1088) by lia. exact POST. }
  clear POST.
  set (vals' := vals ++ junk_vals Rc) in *.
  assert (P0' : vals_ev vals' 0 = sp) by reflexivity.
  run_block_lf HR HK PF1_FUEL [0x14c78] pf1_scr 66%nat.
  clear HR HK. intros Rd Md HR HK EQd LFd. cbn [s_pc s_regs s_log] in HR, EQd, LFd |- *.
  assert (FMd : frame_mod Mc Md (so_regions sp)).
  { rewrite EQd. apply pf1_block_frame; [exact P0' | exact Plo | vm_compute; reflexivity | exact LFd]. }
  clear EQd LFd.
  apply HCONT.
  - (* [comment removed for export] *)
    eapply (keeps_cs_of_same _ pf1_sr _ regs Rd); [ | | exact HR].
    + vm_compute. reflexivity.
    + subst vals'. apply env_app_regs; [rewrite HL; vm_compute; reflexivity | exact HR0].
  - (* [comment removed for export] *)
    eapply frame_mod_trans_same; [|exact FMd]. eapply frame_mod_trans_same; [|exact FMc].
    eapply frame_mod_trans_same; [exact FMa | exact FMb].
  - (* [comment removed for export] *)
    constructor; [cbn; lia | krd_solve HK .. | reflexivity].
Qed.
