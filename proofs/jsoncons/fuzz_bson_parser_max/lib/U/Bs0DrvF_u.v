(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts DivergeSim SpinAlg SpinAlgX
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame
  Spec LibWritev RefNodes RefMemcpyLib RefReadLib RefPrintfLib RefLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0StartupDefs_u Bs0Startup_u Bs0MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Hoare MemSplit Frame.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.musl Require Import Bs0MemcpyBase_u Bs0Memcpy_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ExitBase_u Bs0StdioDefs_u Bs0Exit_u Bs0LibStdioCall_u Bs0LibMainRet_u Bs0PrintfBufBase_u Bs0PrintfBuf_u.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface LibIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Drv_defs_u Bs0DrvLib_u Bs0DrvA_u Bs0DrvB_u Bs0DrvC_defs_u Bs0DrvC_u Bs0DrvD_defs_u Bs0DrvLibL_u Bs0DrvD_u Bs0DrvE_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Local Ltac lia := first [ solve [ try (match goal with H : (length _ <= S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))))))))))))))))))))))%nat |- _ => clear dependent H end); Lia.lia ] | Lia.lia ].

Tactic Notation "run_blockT" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX false.
Tactic Notation "run_blockT_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_T scr NX true.
Tactic Notation "run_blockP_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_P scr NX true.
Tactic Notation "run_blockR_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS_R scr NX true.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
#[using="Type"] Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10c9d) 1 = Some [Z_to_bv 8 10].
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma locale_img : forall k, (k < 6)%nat ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 (0xea288 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros k Hk. do 6 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Section DrvF.
  Context {RE : RunEnv}.
  Variable L : heap_layout.
  Variable HI : heap_iface.
  Hypothesis HIok : heap_iface_ok L scfg HI.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable VM0 : VmMaps.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Variable cr0 : credit.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis DL : drv_layout L sp0.
  Variable CAP : Z.
  Hypothesis HCAP : (65536 <= CAP <= 67108864)%Z.
  Variable crC : credit.
  Hypothesis HLEN : (Z.of_nat (length fdata) < CAP)%Z.
  Variable Lay : lib_layout.
  Variable LSt : lib_statics.
  Hypothesis DLL : drv_lib_layout Lay L.
  Hypothesis LIok : lib_iface_ok Lay scfg HI LSt.
  Hypothesis LSX : forall g M, ls_ok LSt g M -> exists ax : axv, atexit_cells M ax.      (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Huid : (bv_unsigned uid < 2 ^ 32)%Z.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.

  Let Hsp : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z := conj (proj1 Hvsp) (proj1 (proj2 Hvsp)).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).
  Let LEN : Z := Z.of_nat (length fdata).
  Let ENVb (vals : list word) : env := ENV a0s path hw rdraw fdata vals.
  Let above (M : word -> option byte) : Prop := above_sp0 sp0 mem0 M.
  Let model2 (VM : VmMaps) : Model := model2 tid fs0 stdin0 VM.
  Let CFG : Z := CFG fdata.
  Let PL : Z := PL fdata.
  Let CALLS : Z := CALLS fdata.
  Let payload : list byte := payload fdata.
  Let lh_vals := lh_vals sp0 a0s path envv tid fdata.
  Let blk_facts := blk_facts L fdata CAP.
  Let lh1_k := lh1_k scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP crC.
  Let cr1 := cr1 L fdata crC.
  Let relay_regs := relay_regs sp0 a0s path hw rdraw tid mem0 VM0 fs0 stdin0 fdata Hvsp Htid Hplen CAP HCAP.
  Let relay_agree := relay_agree sp0 a0s path hw rdraw fdata Hplen.
  Let relay_len := relay_len sp0 path fdata Hplen.
  Let relay_lo := relay_lo sp0 path fdata Hplen.
  Let relay_81 := relay_81 sp0 path fdata Hplen.
  Let relay_101 := relay_101 sp0 path fdata Hplen.
  Let hiv_facts' := hiv_facts' sp0 a0s path envv uid hw rdraw Hva Hve Hvsp Hplen.
  Let content_block' := content_block' sp0 a0s path hw rdraw fdata Hvsp.
  Let SSP := SSP scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP Lay LSt.
  Let LH2P := LH2P scfg L HI sp0 a0s path envv hw rdraw tid mem0 fs0 stdin0 fdata CAP Lay LSt.
  Let E := E fs0.

  Hypothesis Hok : (6 + CFG <= LEN)%Z.
  (* [comment removed for export] *)
  Hypothesis Hcr2 : credit_le (credit_scale CALLS (ll_credit Lay PL)) cr1.

  #[using="Type"] Lemma m2_but' : forall VM m', model_but_vm (model2 VM) m' -> m' = model2 (m_vmmaps m').
  Proof. intros VM m' H. exact H. Qed.
  #[using="sp0 path Hvsp Hplen CAP HCAP HLEN Hsp LEN CFG CALLS Hok"] Lemma PL_range' : (0 <= PL <= 67108857)%Z.
  Proof. subst PL CFG LEN. unfold Bs0DrvC_u.PL. pose proof (CFG_range fdata). lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition IMG_PW : list (Z * Z) := [(0xb83f0, 0xb84d8); (0xea7a8, 0xeabb0); (0xc8550, 0xc8558)]%Z.
  Definition CPpw (a : Z) : Prop := ((0xb83f0 <= a < 0xb84d8) \/ (0xea7a8 <= a < 0xeabb0) \/ (0xc8550 <= a < 0xc8558) \/ (bv_unsigned sp0 - 8388608 <= a))%Z.

  #[using="Hvsp Hplen Hsp LEN CFG PL CALLS"] Lemma regions_pw : forall vals, vals_ev vals 0 = sp0 ->
    regions_ok RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_PW [] (ENVb vals) CPpw (fun _ => True).
  Proof.
    intros vals P0. pose proof Hsp as Hsp'.
    constructor; cbn [ev ENVb ENV]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold CPpw. lia.
    - intros z Hz. right. exact I.
    - intros i nb Hf. discriminate.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_PW in Hin.
      destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-; (split; [lia|]); (split; [lia|]); intros a Ha; unfold CPpw; lia.
    - intros lo hi [].
  Qed.

  #[using="Hvsp Hplen Hsp LEN CFG PL CALLS"] Lemma mem_pw_frame : forall vals M log (a : Z),
    vals_ev vals 0 = sp0 -> log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_PW log = true ->
    (0 <= a)%Z -> ~ CPpw a ->
    mem_denot (ENVb vals) M log (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof.
    intros vals M log a P0 Hlog Ha Hn. pose proof Hsp as Hsp'.
    apply (mem_denot_frame_Z RSEGS 0 (2 ^ 40) (2 ^ 40) [] [] [] IMG_PW (ENVb vals) CPpw (fun _ => True) [] (regions_pw vals P0) M log a Hlog);
      [unfold CPpw in Hn; lia | exact Hn].
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L HIok Hvsp Hplen DL Lay DLL LIok Hsp LEN CFG PL CALLS"] Lemma block_pw : forall vals M log LB cr VM g,
    vals_ev vals 0 = sp0 ->
    log_in_b 0 (2 ^ 40) (2 ^ 40) [] [] IMG_PW log = true -> log_below_b 0 0xeb000 log = true ->
    (hi_heap HI LB cr M VM -> hi_heap HI LB cr (mem_denot (ENVb vals) M log) VM)
    /\ (above M -> above (mem_denot (ENVb vals) M log))
    /\ (ls_ok LSt g M -> ls_ok LSt g (mem_denot (ENVb vals) M log))
    /\ (forall (a : Z) n bs, hz sp0 a (Z.of_nat n) ->
          rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS (mem_denot (ENVb vals) M log) (Z_to_bv 64 a) n = Some bs).
  Proof.
    intros vals M log LB cr VM g P0 Hlog Hbelow. pose proof Hsp as Hsp'.
    pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    assert (FR : forall a, (0 <= a)%Z -> ~ CPpw a -> mem_denot (ENVb vals) M log (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      by (intros; apply mem_pw_frame; assumption).
    assert (AB : forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem_denot (ENVb vals) M log a = M a).
    { intros a Ha. apply (mem_denot_above (ENVb vals) M log 0%nat 0xeb000 a Hbelow); cbn [ev ENVb ENV]; rewrite ?P0; lia. }
    split; [|split; [|split]].
    - intros HH. apply (hio_frame L scfg HI HIok LB cr M _ VM HH).
      + intros a Ha Hpriv. destruct (Z.le_gt_cases (bv_unsigned sp0) a) as [Hup|Hdown].
        { rewrite <- (u_small a) in Hup by lia. exact (AB (Z_to_bv 64 a) Hup). }
        apply FR; [lia|]. unfold CPpw.
        destruct Hpriv as [[A [_ B]]|A].
        * rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
          assert (~ (0xb8000 <= a < 0xeb000) \/ hl_alloc_static L a)%Z as [C|C]
            by (destruct (Z_lt_ge_dec a 0xb8000); [left; lia|]; destruct (Z_lt_ge_dec a 0xeb000); [|left; lia];
                right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
          -- lia.
          -- apply STA in C. lia.
        * apply RO in A. lia.
      + intros x Hx. exact (mem_denot_grows (ENVb vals) M log x Hx).
    - intros HA a Ha. rewrite AB by exact Ha. apply HA. exact Ha.
    - intros Hls. apply (lio_frame Lay scfg HI LSt LIok g M _ Hls).
      + intros a Ha Hf. apply FR; [lia|]. destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPpw. lia.
      + intros a Ha Hn. pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
        rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; exact Hn | lia | unfold CPpw; lia].
      + intros a Ha Hi. destruct Hi as [(iv & Hin & Hr) | Hi].
        * apply FR; [lia|]. apply (dll_initc Lay L DLL) in Hin. unfold CPpw. lia.
        * rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. rewrite <- (u_small a) in Hi by lia. apply AB. lia.
    - intros a n bs (Ha1 & Ha2 & Ha3) HR. rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; [lia | unfold CPpw; lia].
  Qed.


  (* [comment removed for export] *)
  #[using="scfg L HIok path fdata Hvsp Hplen DL Lay DLL LIok Hsp LEN CFG PL CALLS"] Lemma sw_pw : forall M M' (su : Z) bufp bufsz LB cr VM g,
    sw_post M su 0xb83f0 bufp bufsz M' -> (bv_unsigned sp0 - 8388608 + 112 <= su)%Z -> (su <= bv_unsigned sp0)%Z ->
    (hi_heap HI LB cr M VM -> hi_heap HI LB cr M' VM)
    /\ (above M -> above M')
    /\ (ls_ok LSt g M -> ls_ok LSt g M')
    /\ (forall (a : Z) n bs, hz sp0 a (Z.of_nat n) ->
          rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs).
  Proof.
    intros M M' su bufp bufsz LB cr VM g HP Hlo Hhi. pose proof Hsp as Hsp'.
    pose proof (dl_ro L sp0 DL) as RO. pose proof (dl_static L sp0 DL) as STA.
    pose proof (dl_img_lo L sp0 DL) as IL. pose proof (dl_img_hi L sp0 DL) as IH.
    assert (FR : forall a, (0 <= a < 2 ^ 64)%Z -> ~ CPpw a \/ ((0xb83f0 <= a < 0xb8410) \/ (0xb8420 <= a < 0xb8428) \/ (0xb8430 <= a))%Z /\ (a < su - 112 \/ su <= a)%Z ->
                 M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hc. apply (swp_agree _ _ _ _ _ _ HP); rewrite u_small by lia; unfold CPpw in Hc; lia. }
    split; [|split; [|split]].
    - intros HH. apply (hio_frame L scfg HI HIok LB cr M M' VM HH).
      + intros a Ha Hpriv. apply FR; [exact Ha|]. unfold CPpw.
        destruct Hpriv as [[A [_ B]]|A].
        * rewrite (dl_sptop L sp0 DL) in A. rewrite IL, IH in B.
          assert (~ (0xb8000 <= a < 0xeb000) \/ hl_alloc_static L a)%Z as [C|C]
            by (destruct (Z_lt_ge_dec a 0xb8000); [left; lia|]; destruct (Z_lt_ge_dec a 0xeb000); [|left; lia];
                right; apply Classical_Prop.NNPP; intros Hn; apply B; split; [lia| exact Hn]).
          -- left. lia.
          -- apply STA in C. left. lia.
        * apply RO in A. lia.
      + exact (swp_grows _ _ _ _ _ _ HP).
    - intros HA a Ha. pose proof (u64_range a). rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; apply HA; exact Ha | lia | right; lia].
    - intros Hls. apply (lio_frame Lay scfg HI LSt LIok g M M' Hls).
      + intros a Ha Hf. apply FR; [exact Ha|]. destruct Hf as (iv & Hin & Hr). apply (dll_foot Lay L DLL) in Hin. unfold CPpw. left. lia.
      + intros a Ha Hn. pose proof (dll_rw_lo Lay L DLL). pose proof (u64_range a).
        rewrite <- (Z_to_bv_bv_unsigned 64 a), FR; [rewrite Z_to_bv_bv_unsigned; exact Hn | lia | unfold CPpw; left; lia].
      + intros a Ha Hi. apply FR; [exact Ha|]. destruct Hi as [(iv & Hin & Hr) | Hi].
        * apply (dll_initc Lay L DLL) in Hin. unfold CPpw. left. lia.
        * rewrite (dll_heap Lay L DLL), (dl_sptop L sp0 DL) in Hi. right. lia.
    - intros a n bs (Ha1 & Ha2 & Ha3) HR. rewrite <- HR. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply FR; [lia | unfold CPpw; left; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac kimg1 lo n := let HK := match goal with H : know_ok _ _ _ knLc1 |- _ => H end in
    let KI := fresh "KI" in
    pose proof (know_nth RSEGS _ _ knLc1 ltac:(let q := kidx knLc1 (is_kimg_cov lo n) in exact q) _ HK eq_refl) as KI;
    cbn [kentry_ok] in KI; destruct KI as (_ & _ & KI); apply KI; lia.
  #[using="L regs0 Hva Hve Hvsp Htid ME Hplen DL DLL Huid Hfits Hsp LEN CFG PL CALLS"] Lemma init_facts : forall vals M,
    vals_ev vals 0 = sp0 -> vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
    know_ok RSEGS (ENVb vals) M knLc1 -> above M ->      (* [comment removed for export] *)
    lib_init_facts Lay (bv_unsigned (auxvp sp0 a0s path envv)) (bv_unsigned uid) (bv_unsigned (rnd sp0 a0s path envv)) (bv_unsigned tid)
                   (CANZ rdraw) (bv_unsigned hw) M.
  Proof.
    intros vals M P0 P3 P4 P5 HK HA. pose proof Hsp as Hsp'.
    destruct (auxvp_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as [AV1 AV2].
    destruct (rnd_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as (RN1 & RN2 & RN3 & RN4).
    pose proof (auxv_off_bound RPH sp0 rdraw [a0s; path] envv uid hw) as AOB.
    pose proof (build_stack_bytes_within_span RPH sp0 [a0s; path] envv uid hw rdraw) as BSB.
    pose proof Hfits as FIT. unfold entry_stack_fits, sp_window_hi in FIT.
    pose proof (u64_range (auxvp sp0 a0s path envv)) as AVR. pose proof (u64_range (rnd sp0 a0s path envv)) as RNR.
    pose proof (u64_range uid) as UR. pose proof (u64_range hw) as HWR. pose proof (CANZ_range rdraw) as CR.
    assert (KC : forall addr, kblob_find knLc1 (ELit 0) addr = Some (ELit 8, 2%nat) ->
                 rdn RSEGS M (Z_to_bv 64 addr) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (CANZ rdraw)))).
    { intros addr Hc. unfold CANZ. rewrite Z_to_bv_bv_unsigned.
      pose proof (kblob_rdn RSEGS (ENVb vals) M knLc1 (ELit 0) addr (ELit 8) 2%nat HK Hc) as R.
      unfold adenot, v_addi in R. cbn [a_base a_off edenot eb ENVb ENV blobs_ev nth app blobs0] in R.
      rewrite length_word_to_le_bytes, u_small in R by lia. rewrite Z.add_0_l in R. exact R. }
    unfold lib_init_facts. rewrite (dll_heap Lay L DLL), (dl_segs L sp0 DL), (dl_sptop L sp0 DL), (dll_init_img Lay L DLL),
      (dll_td_self Lay L DLL), (dll_td_tid Lay L DLL), (dll_td_locale Lay L DLL), (dll_locale Lay L DLL), (dll_td_canary Lay L DLL),
      (dll_guard Lay L DLL), (dll_auxvp Lay L DLL). cbv zeta. unfold cellz.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]]]]]].
    - (* [comment removed for export] *)
      intros iv a Hin Hr.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; cbn [fst snd] in Hr.
      + kimg1 0x10000%Z 16%Z. + kimg1 0xc8551%Z 3%Z. + kimg1 0xc8555%Z 0x199b%Z. + kimg1 0xe9fc8%Z 0x20%Z.
      + kimg1 0xea008%Z 8%Z. + kimg1 0xea014%Z 4%Z. + kimg1 0xea020%Z 8%Z. + kimg1 0xea030%Z 0xf8%Z. + kimg1 0xea130%Z 0xf8%Z.
      + kimg1 0xea253%Z 1%Z. + kimg1 0xea328%Z 4%Z.
    - krd_solve HK.
    - krd HK 0xc9f18%Z 4%nat Htc. rewrite Htc. cbn [ev ENVb ENV]. rewrite P5.
      rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - lia.
    - krd_solve HK.
    - intros k Hk. rewrite (kimg_rdn RSEGS _ _ knLc1 ltac:(let q := kidx knLc1 (is_kimg_cov 0xea288 48) in exact q) _ _ (0xea288 + 8 * Z.of_nat k) 8 HK eq_refl) by lia.
      apply locale_img. exact Hk.
    - apply KC. vm_compute. reflexivity.
    - apply KC. vm_compute. reflexivity.
    - lia.
    - krd HK 0xea258%Z 8%nat Hav. rewrite Hav. cbn [ev ENVb ENV]. rewrite P3, Z_to_bv_bv_unsigned. reflexivity.
    - lia.
    - lia.
    - pose proof (know_nth RSEGS _ _ knLc1 ltac:(let q := kidx knLc1 (kentry_eqb (KAlign (EVar 3) 8)) in exact q) _ HK eq_refl) as KA.
      cbn [kentry_ok edenot ev ENVb ENV] in KA. rewrite P3 in KA. destruct KA as [_ KA]. exact KA.
    - intros j Hj.
      transitivity (rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8).
      + apply rdn_agree. intros q Hq. apply HA. rewrite (u_small (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) by lia.
        rewrite u_small by lia. lia.
      + rewrite (auxv_word_at sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME j Hj).
        f_equal. f_equal. unfold auxv_words. rewrite (dll_phdr Lay L DLL), (dll_phent Lay L DLL), (dll_phnum Lay L DLL).
        do 20 (destruct j as [|j]; [cbn; rewrite ?Z_to_bv_bv_unsigned; reflexivity|]). lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - (* [comment removed for export] *)
      rewrite (dll_init_cells Lay L DLL).
      repeat (apply Forall_cons; [cbn [fst snd]; unfold cellz;
        lazymatch goal with |- rdn _ _ _ (Z.to_nat ?n) = _ => let k := eval vm_compute in (Z.to_nat n) in change (Z.to_nat n) with k end;
        krd_solve HK |]).
      apply Forall_nil.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HIok uid regs0 VM0 Hva Hve Hvsp Htid ME Hplen DL HCAP HLEN DLL LIok Huid Hfits Hsp Hal LEN ENVb above model2 CFG PL payload cr1 relay_regs relay_agree relay_len relay_lo relay_81 relay_101 hiv_facts' Hok Hcr2"] Lemma iter1 : forall K, K [] -> SSP CALLS 0 K -> lh1_k (t_emit (W 1 (zero_lines 1)) K).
  Proof.
    intros K HK0 HSS. unfold lh1_k, Bs0DrvD_u.lh1_k.
    intros fx' vals R M VM A1 PTR OWN LB (HL & P0 & P1 & P2 & P3 & P4 & P5 & P48 & P70 & P73 & P79 & P81 & P82 & P83)
           HR HK HA HBLK HC HPAY HH.
    fold payload in HPAY. fold PL CALLS in P81. fold PL in P79. fold CFG in P73. fold cr1 in HH.
    pose proof Hsp as Hsp'. pose proof Hal as Hal'.
    pose proof (hiv_facts' vals P3 P4) as HIV.
    destruct HBLK as [HBR REST]. unfold Bs0DrvD_u.blk_facts in REST. fold PL in REST.
    pose proof (hz_of_block_range L sp0 DL _ _ HBR) as HZ. pose proof HZ as (Q1 & Q2 & Q4).
    pose proof PL_range' as HPr. pose proof (payload_len fdata) as PLN. fold PL in PLN. fold payload in PLN.
    pose proof (dll_credit_pos Lay L DLL PL ltac:(lia)) as [CP1 CP2]. pose proof (CALLS_range fdata) as HKr. fold CALLS in HKr.
    assert (HKe : t_emit (W 1 (zero_lines 1)) K []) by apply t_emit_has_nil.
    (* [comment removed for export] *)
    change (ENV a0s path hw rdraw fdata vals) with (ENVb vals) in HR, HK.
    run_blockT_keep scr0 102%nat.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
      destruct (block_pw vals M lg LB cr1 VM (ls_g0 LSt) P0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH) as HH0. pose proof (BA HA) as HA0.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC) as HC0.
    assert (HPAY0 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY). }
    clear BH BA BL BRd EQM HH HA HC HPAY. rename HH0 into HH. rename HA0 into HA. rename HC0 into HC. rename HPAY0 into HPAY.
    clear M. rename M0 into M.
    (* [comment removed for export] *)
    pose proof (lio_init Lay scfg HI LSt LIok _ _ _ _ _ _ M (init_facts vals M P0 P3 P4 P5 HK HA)) as Hls0.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
    eapply (lib_site scfg L HI HIok sp0 Hsp' Hal' DL Lay LSt DLL LIok vals _ srLB knLc1 Rc M (model2 VM) LB cr1 (ls_g0 LSt) (-208)
              [(48%nat, 65536%Z)] [] PTR 0x34618 payload (t_emit (W 1 (zero_lines 1)) K));
      [ exact HR | exact HK
      | rewrite HL; vm_compute; reflexivity | rewrite HL; vm_compute; reflexivity | rewrite HL; lia
      | exact P0 | exact HIV | vm_compute; reflexivity
      | regv HR (2 : reg); cbn [edenot ev ENVb ENV]; rewrite P0; apply alu_add_w_lit
      | lia | reflexivity
      | regv HR (1 : reg); reflexivity | lia | reflexivity
      | regv HR (3 : reg); reflexivity | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); cbn [edenot ev ENVb ENV]; exact P82
      | regv HR (11 : reg); cbn [edenot ev ENVb ENV]; rewrite P79, PLN; f_equal; lia
      | rewrite PLN; lia
      | destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)];
        [ left; split; [rewrite PLN; lia | exact HPTR] | right; split; [rewrite PLN; lia|]; subst LB PTR; left; rewrite PLN; f_equal; lia ]
      | exact HPAY
      | rewrite PLN; replace (Z.of_nat (Z.to_nat PL)) with PL by lia; exact (credit_le_head sp0 Hsp' CALLS (ll_credit Lay PL) cr1 ltac:(lia) CP1 CP2 Hcr2)
      | exact Hls0
      | exact HH | reflexivity | reflexivity | reflexivity
      | intros i nb Hf; cbn in Hf;
        destruct (Nat.eqb i 48) eqn:Ei; [apply Nat.eqb_eq in Ei; subst i; injection Hf as <-; split; [rewrite HL; lia|];
                                         rewrite P48, u_small by lia; exists CAP; split; [lia|]; split; [| exact HBR];
                                         destruct REST as [(_ & _ & _ & ->) | (_ & _ & _ & _ & ->)]; [left | right; left]; reflexivity
                                       | discriminate]
      | intros v b Hf; discriminate
      | exact HKe | ]
    end.
    clear HR HK Hls0.
    intros fx2 R' M' model' g' cr' vals' E' HL' HR HK HH' HBUT Hls' Hcr' HAB HBLK' HIMG. subst vals' E'.
    rewrite (m2_but' _ _ HBUT). rewrite (m2_but' _ _ HBUT) in HH'. cbn [m_vmmaps Bs0DrvB_u.model2 mkModelE with_net with_creds mkModel m_vm vmst_maps] in HH'.
    set (VM2 := m_vmmaps model') in *. clearbody VM2.
    rewrite HL in HR, HL'. change (keep_lib (-208) [(48%nat, 65536%Z)] [] knLc1) with knLr1 in HK.
    set (vals2 := vals ++ junk_vals R') in *.
    change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals2) in HR, HK.
    assert (XL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals2 q = x).
    { intros q x Hq Hx. subst vals2. rewrite vals_ev_app_l by (rewrite HL; exact Hq). exact Hx. }
    pose proof (XL 0%nat _ ltac:(lia) P0) as X0. pose proof (XL 3%nat _ ltac:(lia) P3) as X3. pose proof (XL 4%nat _ ltac:(lia) P4) as X4.
    pose proof (XL 5%nat _ ltac:(lia) P5) as X5. pose proof (XL 48%nat _ ltac:(lia) P48) as X48.
    pose proof (hiv_facts' vals2 X3 X4) as HIV2.
    assert (HA2 : above M') by (intros a Ha; rewrite HAB by exact Ha; apply HA; exact Ha).
    assert (HC2 : rdn RSEGS M' (Z_to_bv 64 A1) (length fdata) = Some fdata).
    { rewrite <- HC. apply rdn_agree. intros q Hq. rewrite u_small by lia. apply HBLK'; [lia|].
      exists (A1, CAP). split; [destruct REST as [(_ & _ & _ & ->)|(_ & _ & _ & _ & ->)]; [left|right; left]; reflexivity|]. cbn [fst snd]. lia. }
    assert (HPAY2 : rdn RSEGS M' (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4).
        rewrite <- HPAY. apply rdn_agree. intros q Hq. rewrite PLN in Hq. rewrite u_small by lia. apply HBLK'; [lia|].
        exists (OWN, PL). subst LB PTR. split; [left; reflexivity|]. cbn [fst snd]. lia. }
    clear HA HC HPAY HAB HBLK' HIMG HH.
    (* [comment removed for export] *)
    run_blockT_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
      destruct (block_pw vals2 M' lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH') as HH'c. pose proof (BA HA2) as HA2c. pose proof (BL Hls') as Hls'c.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC2) as HC2c.
    assert (HPAY2c : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
    clear BH BA BL BRd EQM HH' HA2 Hls' HC2 HPAY2.
    rename HH'c into HH'. rename HA2c into HA2. rename Hls'c into Hls'. rename HC2c into HC2. rename HPAY2c into HPAY2.
    clear M'. rename M0 into M'.
    (* [comment removed for export] *)
    run_blockP_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ _ ?lg =>
      destruct (block_pw vals2 M' lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH') as HH1. pose proof (BA HA2) as HA1. pose proof (BL Hls') as Hls1.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC2) as HC1.
    assert (HPAY1 : rdn RSEGS M0 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
    clear BH BA BL BRd EQM HH' HA2 Hls' HC2 HPAY2.
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
      eapply (rz_ioctl_winsz RSEGS scfg Rc _ Mc (model2 VM2) ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | reflexivity | reflexivity
      | regv HR (17 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | reflexivity
      | reflexivity
      | regv HR (11 : reg); reflexivity
      | ]
    end.
    rewrite v_addi_pc4 by lia. change (0xa097c + 4)%Z with 0xa0980%Z.
    pose proof (regs_set_a0 (ENVb vals2) _ _ (errno_ret ENOTTY) (ELit 18446744073709551591) HR ltac:(apply bv_eq; reflexivity)) as HR1.
    clear HR. rename HR1 into HR.
    (* [comment removed for export] *)
    run_blockP_keep scr0 134%nat.
    lazymatch type of EQM with _ = mem_denot _ ?mp ?lg =>
      destruct (block_pw vals2 mp lg LB cr' VM2 g' X0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    pose proof (BH HH1) as HH2. pose proof (BA HA1) as HA2. pose proof (BL Hls1) as Hls2.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC1) as HC2.
    assert (HPAY2 : rdn RSEGS M1 (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY1). }
    clear BH BA BL BRd EQM HH1 HA1 Hls1 HC1 HPAY1.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
      assert (HSC : stdio_call 134 sr kn = Some scP) by (vm_compute; reflexivity);
      pose proof (stdio_call_sound_fr scfg vals2 _ sr kn Rc Mc (model2 VM2) scP [Z_to_bv 8 48] [Z_to_bv 8 10] K HR HK
                    (eq_trans (f_equal (fun n => stdio_call n sr kn) HL') HSC)) as Hsc;
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scP length app Z.of_nat Pos.of_succ_nat Pos.succ] in Hsc;
      unfold W; cbn [map zero_lines app];
      apply Hsc; clear Hsc HSC;
      [ cbn [edenot]; rewrite !u_small by lia; lia
      | cbn [edenot]; rewrite !u_small by lia; lia
      | cbn [edenot]; rewrite !u_small by lia; reflexivity
      | cbn [edenot]; lit_u; reflexivity
      | cbn; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV]; rewrite X0; rewrite ?u_small by lia; lia
      | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVb ENV]; rewrite X0; rewrite ?u_small by lia; lia
      | cbn [edenot]; rewrite ?u_small by lia; lia
      | cbn [edenot]; rewrite !u_small by lia; krd_solve HK
      | cbn [edenot]; rewrite (kimg_rdn RSEGS _ _ kn ltac:(let q := kidx kn (is_kimg_cov 0x10c9d 1) in exact q) _ _ 0x10c9d 1 HK eq_refl) by (cbn; lia);
        apply nl_img
      | reflexivity
      | reflexivity
      | reflexivity
      | exact HK0
      | ]
    end end.
    clear HR HK.
    intros RW MW HR HK HP.
    rewrite edenot_add_lit in HP. unfold adenot, v_addi in HP. cbn [a_base a_off edenot ev ENVb ENV] in HP. rewrite X0 in HP.
    destruct (sw_pw M1 MW _ _ _ LB cr' VM2 g' HP ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; lia)) as (SH & SA & SL & SRd).
    pose proof (SH HH2) as HH3. pose proof (SA HA2) as HA3. pose proof (SL Hls2) as Hls3.
    pose proof (SRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC2) as HC3.
    assert (HPAY3 : rdn RSEGS MW (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (SRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY2). }
    clear SH SA SL SRd HP HH2 HA2 Hls2 HC2 HPAY2.
    try rewrite HL' in HR. try rewrite HL' in HK.
    set (vals3 := vals2 ++ junk_vals RW) in *.
    assert (HL3 : length vals3 = 166%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL'; reflexivity).
    change (Env (vals_ev vals3) (blobs_ev (blobs0 a0s path hw rdraw ++ [fdata]))) with (ENVb vals3) in HR, HK.
    assert (YL : forall q x, (q < 102)%nat -> vals_ev vals q = x -> vals_ev vals3 q = x).
    { intros q x Hq Hx. subst vals3. rewrite vals_ev_app_l by (rewrite HL'; lia). apply XL; assumption. }
    pose proof (YL 0%nat _ ltac:(lia) P0) as Y0. pose proof (YL 3%nat _ ltac:(lia) P3) as Y3. pose proof (YL 4%nat _ ltac:(lia) P4) as Y4.
    pose proof (hiv_facts' vals3 Y3 Y4) as HIV3.
    (* [comment removed for export] *)
    run_blockR_keep scr0 166%nat.
    lazymatch type of EQM with _ = mem_denot _ ?mp ?lg =>
      destruct (block_pw vals3 mp lg LB cr' VM2 g' Y0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (BH & BA & BL & BRd) end.
    rewrite <- EQM in BH, BA, BL, BRd.
    lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ => rename Rc into RS; rename Mc into MS end.
    pose proof (BH HH3) as HH4. pose proof (BA HA3) as HA4. pose proof (BL Hls3) as Hls4.
    pose proof (BRd A1 (length fdata) fdata ltac:(eapply (hz_sub sp0); [exact HZ | lia | lia | unfold LEN in HLEN; lia]) HC3) as HC4.
    assert (HPAY4 : rdn RSEGS MS (Z_to_bv 64 PTR) (length payload) = Some payload).
    { destruct REST as [(HPL0 & HPTR & HOWN & HLB) | (HPLp & HPTR & HBR2 & HAP & HLB)].
      - assert (Hp0 : payload = []) by (apply length_zero_iff_nil; rewrite PLN; lia). rewrite Hp0. reflexivity.
      - pose proof (hz_of_block_range L sp0 DL _ _ HBR2) as HZ2. pose proof HZ2 as (U1 & U2 & U4). subst PTR.
        apply (BRd OWN (length payload) payload ltac:(eapply (hz_sub sp0); [exact HZ2 | lia | lia | rewrite PLN; lia]) HPAY3). }
    clear BH BA BL BRd EQM HH3 HA3 Hls3 HC3 HPAY3.
    (* [comment removed for export] *)
    set (valsS := relay vals3 RS (Z_to_bv 64 (WP 0))).
    apply (HSS fx2 valsS RS MS VM2 A1 PTR OWN LB cr' g').
    - unfold lh_vals, Bs0DrvD_u.lh_vals. subst valsS. rewrite (relay_len vals3 RS _ ltac:(lia)), relay_81 by lia.
      rewrite !(relay_lo vals3 RS _) by lia.
      repeat split; try (apply YL; [lia | assumption]).
      + unfold relay. change 82%nat with (81 + 1)%nat. rewrite vals_hi by lia. cbn [nth lay_ext]. regv HR (9 : reg). cbn [edenot ev ENVb ENV]. apply YL; [lia | exact P82].
      + unfold relay. change 83%nat with (81 + 2)%nat. rewrite vals_hi by lia. cbn [nth lay_ext]. regv HR (18 : reg). cbn [edenot ev ENVb ENV]. apply YL; [lia | exact P83].
    - subst valsS. unfold relay. change 84%nat with (81 + 3)%nat. rewrite vals_hi by lia. cbn [nth lay_ext]. regv HR (19 : reg). reflexivity.
    - subst valsS. apply relay_101. lia.
    - cbn [Z.of_nat]. lia.
    - lia.
    - subst valsS. eapply (relay_regs vals3 srR RS _ ltac:(lia)); [vm_compute; reflexivity | exact HR].
    - (* [comment removed for export] *)
      subst valsS.
      assert (HK2 : know_ok RSEGS (ENVb vals3) MS (wposK (ELit 0xea7b0) :: flagsK :: knR2)) by (eapply ksubl_sound; [exact HK | vm_compute; reflexivity]).
      pose proof (Forall_inv HK2) as K1. pose proof (Forall_inv (Forall_inv_tail HK2)) as K2. pose proof (Forall_inv_tail (Forall_inv_tail HK2)) as K3.
      unfold knLH2. constructor; [|constructor; [|constructor]].
      + cbn [kentry_ok] in K1 |- *. destruct K1 as (K1a & K1b & K1c). split; [exact K1a|]. split; [apply flat_abs0; lia|].
        rewrite SymDriveX.adenot_lit0 in K1c |- *. cbn [edenot ev ENVb ENV] in K1c |- *. rewrite relay_101 by lia. exact K1c.
      + cbn [kentry_ok edenot ev ENVb ENV]. rewrite relay_101 by lia. unfold WP. rewrite u_small by lia. lia.
      + exact K2.
      + eapply (know_ok_agree RSEGS 82); [apply relay_agree; lia | vm_compute; reflexivity | exact K3].
    - exact HA4.
    - split; [exact HBR | exact REST].
    - exact HC4.
    - exact HPAY4.
    - reflexivity.
    - exact HH4.
    - rewrite PLN in Hcr'. replace (Z.of_nat (Z.to_nat PL)) with PL in Hcr' by lia.
      exact (credit_le_step sp0 Hsp' CALLS (ll_credit Lay PL) cr1 cr' ltac:(lia) CP1 CP2 Hcr2 Hcr').
    - exact Hls4.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HIok VM0 Hva Hve Hvsp Htid Hplen DL HCAP crC HLEN DLL LIok LSX Hsp LEN CFG PL CALLS cr1 Hok"] Lemma SS_real : forall (n j : nat), (1 <= n)%nat -> (Z.of_nat j + Z.of_nat n <= 4)%Z -> SSP (Z.of_nat n) j (E (j + n - 1)%nat).
  Proof.
    induction n as [|n IH]; intros j Hn Hjn; [lia|].
    destruct n as [|n'].
    - replace (j + 1 - 1)%nat with j by lia. change (Z.of_nat 1) with 1%Z.
      apply last_S; assumption.
    - apply step_S; try assumption; [lia|].
      replace (Z.of_nat (S (S n')) - 1)%Z with (Z.of_nat (S n')) by lia.
      apply iter2; try assumption; [lia | unfold E, Bs0DrvE_u.E; apply t_emit_has_nil |].
      replace (j + S (S n') - 1)%nat with (S j + S n' - 1)%nat by lia. apply IH; lia.
  Qed.

  #[using="HIok uid regs0 VM0 Hva Hve Hvsp Htid ME Hplen DL HCAP HLEN Lay LSt DLL LIok LSX Huid Hfits Hsp Hal LEN ENVb above model2 CFG PL payload cr1 relay_regs relay_agree relay_len relay_lo relay_81 relay_101 hiv_facts' SSP E Hok Hcr2"] Theorem drv_loop : lh1_k (t_emit (W 1 (zero_lines (Z.to_nat CALLS))) (t_exit (exit_code 0) fs0)).
  Proof.
    pose proof (CALLS_range fdata) as HKr. fold CALLS in HKr.
    set (n := Z.to_nat CALLS). assert (En : Z.of_nat n = CALLS) by (subst n; lia). clearbody n.
    assert (H1 : lh1_k (t_emit (W 1 (zero_lines 1)) (E (0 + n - 1)%nat))).
    { apply iter1; [unfold E, Bs0DrvE_u.E; apply t_emit_has_nil|]. rewrite <- En. apply SS_real; lia. }
    unfold lh1_k, Bs0DrvD_u.lh1_k in H1 |- *. intros fx' vals R M VM A1 PTR OWN LB HLV HR HK HA HBLK HC HPAY HH.
    eapply srz_conseq; [eapply H1; eassumption|].
    unfold E, Bs0DrvE_u.E. eapply t_eq_trans; [apply t_emit_W_app|].
    replace (zero_lines 1 ++ zero_lines (0 + n - 1)) with (zero_lines n); [apply t_eq_refl|].
    destruct n as [|m]; [lia|]. replace (0 + S m - 1)%nat with m by lia. reflexivity.
  Qed.

End DrvF.
End FPX_1.
