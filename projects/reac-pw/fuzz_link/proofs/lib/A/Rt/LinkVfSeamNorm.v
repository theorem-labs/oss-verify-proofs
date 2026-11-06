(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): the memory-FILE pieces of the GXA seam of musl
   vfprintf (LinkVfSeam.v) on the per-call normalized store FMgxaSeamNorm.cjnormv ly R, and the arguments.

   FMgxaSeamNorm.v moves the walk, the store premises and the post between the harness's store and cjnormv ly R
   generically; what it states for musl vsnprintf's FILE, cookie, destination and guard is replaced here by the
   memory FILE's:
   1. the FILE's 232 bytes and its buffer, as cells, carry to cjnormv (cells_cjnormv_high): they are application
      memory above GLOBALS_TOP and below TASK_SIZE, where cjnormv keeps every byte (NM.cj_kept_high,
      NM.sd_kept_app);
   2. GXA's guard vf_mf_guard at cjnormv from the harness's facts (vf_mf_guard_cjnormv, the twin of
      NM.vf_ready_cjnormv);
   3. GXA's post (LinkVfMfA.vfprintf_mf_a_post) read at the harness's final store (vf_mf_post_store,
      post_from_norm_mf_v, the twin of NM.vf_post_store / NM.post_from_norm_v): every conjunct but mem_inv
      (which comes back only where the harness's store had it) and the walk's invariant (True here);
   4. GX's argument list for the memory FILE (args_ok_of_pf_args_asan_mf, the twin of
      FMgxaSeamFam.args_ok_of_pf_args_asan): the regions the call writes are its window and the FILE block,
      vmf_out K sp f = [(sp - K, K); (f, 1304)], and GXA's FILE geometry is Fp = f, B = f + 280, BS = 1024 with
      the two empty regions RC = lo, RCS = 0 and RE = 1, RES = 0 (LinkVfMfA.v vfprintf_mf_a_stmt). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YP02 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require
PropExec MState Mem Exec Frame Cells Step FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require G_pad G_pop_arg G_fmt_fp_lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require
Printf_model G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require
AsanFacts G_printf_core_common G_vfprintf_snf LinkVfMfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMgxaSeamBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require mf_sink_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMgxaSeamCall FMgxaSeamNormG FMgxaSeamNorm FMgxaSeamFam
  FMgxaSeamPf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkVfSeamGuard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module MN := OSSVerify.Proofs.reac_pw.fuzz_link.lib.MemNorm.
Module CJP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.PropExec.
Module CJMS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.MState.
Module CJM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Module CJC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Cells.
Module CJS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.
Module CJFP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.FP.
Module PR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec.Prelim.
Module FF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec.FmtFp.
Module GPAD := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G.G_pad.
Module GFP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G.G_fmt_fp_lib.
Module PM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.Printf_model.
Module GXI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module AF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Module GC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GV := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GMF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.LinkVfMfA.
Module MFS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.mf_sink_c.
Module NG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNormG.
Module NM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNorm.
Module FAM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamFam.
Module LSG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamGuard.

#[local] Existing Instance N_img_asan_vf.

(* ===================================================================================== *)
(* 1. cells above GLOBALS_TOP                                                              *)
(* ===================================================================================== *)

Lemma cells_cjnormv_high : forall ly R H mem A cs,
  @GXI.GLOBALS_TOP N_img_asan_vf <= A -> A + Z.of_nat (CJC.cells_size cs) <= TASK_SIZE ->
  AF.app_ivl A (A + Z.of_nat (CJC.cells_size cs)) ->
  CJS.rw_cells tfibsegs (cjstore H mem) A cs -> CJS.rw_cells tfibsegs (NM.cjnormv ly R H mem) A cs.
Proof.
intros ly R H mem A cs H1 H2 HA HC.
exact (NM.rw_cells_cjnormv ly R H mem A cs (NM.sd_kept_app ly R _ _ (NM.cj_kept_high _ _ H1 H2) HA) HC).
Qed.

(* ===================================================================================== *)
(* 2. the guard at the VIS0-aware store                                                    *)
(* ===================================================================================== *)

Lemma vf_mf_guard_cjnormv : forall copy_ready set_ready strn_ready ly R H mem (q lo f A : Z)
    (fmt : list Z) (slots : list word) (args : list PM.parg),
  AF.pf_rng (cjstore H mem) A (PR.zlength fmt) -> NM.sh_kept ly R A (PR.zlength fmt) ->
  AF.musl_prefix_addressable (cjstore H mem) -> NM.sh_kept ly R (@sym N_img_asan_vf 0x1029e) 9 ->
  GV.args_pf (cjstore H mem) slots args -> NM.args_kept ly R slots args ->
  AF.app_ivl lo q -> AF.app_ivl f (f + 232) -> AF.app_ivl (f + 280) (f + 1304) ->
  lo + GC.OUT_DEPTH <= q - 368 ->
  LSG.seam_calls_ready_mf copy_ready set_ready strn_ready (NM.cjnormv ly R H mem) q lo f ->
  GMF.vf_mf_guard set_ready strn_ready copy_ready FMgxaSeamCall.SEAM_INV (NM.cjnormv ly R H mem) q lo f A fmt
    slots args.
Proof.
intros copy_ready set_ready strn_ready ly R H mem q lo f A fmt slots args PF KF PRE KP APF KA ALO AF1 AB GEO READY.
apply LSG.vf_mf_guard_holds;
  [exact (NM.pf_rng_cjnormv _ _ _ _ _ _ KF PF) | exact (NM.musl_prefix_cjnormv _ _ _ _ KP PRE)
  | exact (NM.args_pf_cjnormv _ _ _ _ _ _ KA APF) | exact ALO | exact AF1 | exact AB | exact GEO | exact READY].
Qed.

(* ===================================================================================== *)
(* 3. the post                                                                             *)
(* ===================================================================================== *)

(* GXA's post (LinkVfMfA.vfprintf_mf_a_post) at the store m the harness's run started from, without mem_inv and
   without the walk's invariant *)
Definition vf_mf_post_store (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (f k : Z) (fl : word) (jp jc : list byte) (we : word) (j48 j64 j104 : list byte) (mode lbf : word)
    (jx pb : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32)
                    (bj : list byte) (m' : word -> option byte),
    ms' = CJMS.MS (CJF.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                           s10 s11 t3 t4 t5 t6)
                  Ft (CJMS.ret_pc ra) fc' None m' (CJP.seg_rom tfibsegs)
    /\ CJF.munch [(lo, bv_unsigned sp); (f, f + 232); (f + 280, f + 1304)] m m'
    /\ CJF.wmono tfibsegs m m'
    /\ CJFP.frm0 fc'
    /\ (forall rk : bv 5, bv_unsigned rk <> 10 -> reg_get Ft rk = reg_get F rk)
    /\ CJF.stk tfibsegs m' lo (bv_unsigned sp)
    /\ GPAD.ssp_cells m' canary
    /\ CJS.rw_cells tfibsegs m' f
         (MFS.mf_file fl jp jc (Z_to_bv 64 (f + 1304)) (Z_to_bv 64 (f + 280 + k + PR.zlength o)) j48
            (Z_to_bv 64 (f + 280)) j64 (f + 280) j104 (if bv_unsigned we =? 0 then Z_to_bv 64 4294967295 else mode)
            lbf jx)
    /\ CJS.rw_cells tfibsegs m' (f + 280) [CJC.CB (length (pb ++ GFP.zb o)) (pb ++ GFP.zb o); CJC.CB (length bj) bj]
    /\ 0 <= r <= FF.INT_MAX.

Theorem post_from_norm_mf_v : forall (INV : (word -> option byte) -> Prop) ly R H mem
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (f k : Z) (fl : word) (jp jc : list byte) (we : word) (j48 j64 j104 : list byte) (mode lbf : word)
    (jx pb : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (s st0 : machine_state),
  MN.ro_agree tfibsegs (cjstore H mem) ->
  NG.gms_rel tfibsegs (NM.seam_drop ly R) s st0 -> NG.gcj_same (NM.seam_drop ly R) (cjstore H mem) (ms_mem s) ->
  GMF.vfprintf_mf_a_post INV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F f k fl jp jc we j48 j64 j104
    mode lbf jx pb r o lo canary (NM.cjnormv ly R H mem) st0 ->
  vf_mf_post_store ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F f k fl jp jc we j48 j64 j104
    mode lbf jx pb r o lo canary (cjstore H mem) s.
Proof.
intros INV ly R H mem ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F f k fl jp jc we j48 j64 j104 mode lbf jx pb
  r o lo canary s st0 Hro Hrel Hsame HP.
destruct HP as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & bj & m0' &
                E & MU & WM & _ & FRM & FOK & ST & SSP & FC & BUF & Hr & _).
assert (Rl : NG.gmem_rel tfibsegs (NM.seam_drop ly R) (ms_mem s) m0').
{ destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & Rl). subst st0. exact Rl. }
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', bj, (ms_mem s).
split; [exact (NM.ms_from_norm_v ly R s st0 _ _ _ _ _ m0' _ Hrel E)|].
split; [exact (NM.munch_from_norm_v ly R H mem _ m0' _ Hro Rl Hsame MU)|].
split; [exact (NM.wmono_from_norm_v ly R H mem _ m0' Hro Rl Hsame WM)|].
split; [exact FRM|]. split; [exact FOK|].
split; [exact (NM.stk_from_rel_v ly R _ m0' _ _ Rl ST)|].
split; [exact (NM.ssp_cells_from_rel_v ly R _ m0' _ Rl SSP)|].
split; [exact (NM.rw_cells_from_rel_v ly R _ m0' _ _ Rl FC)|].
split; [exact (NM.rw_cells_from_rel_v ly R _ m0' _ _ Rl BUF)|].
exact Hr.
Qed.

(* ===================================================================================== *)
(* 4. the arguments                                                                        *)
(* ===================================================================================== *)

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the rs shape is LinkVfDefs.vmf_out K sp f with lo = sp - K, q = sp *)
Lemma args_ok_of_pf_args_asan_mf :
  forall H mem (rs : list (Z * Z)) ws args (f lo q : Z),
    pf_args_asan (aview tfibsegs H mem) rs ws args ->
    pf_args_slack ws args ->
    (forall u, In (AU64 u) args -> 0 <= u < 2 ^ 64) ->
    rs = [(lo, q - lo); (f, 1304)] -> lo + 8 <= q ->
    @GXI.args_ok N_img_asan_vf f (f + 280) 1024 lo 0 1 0 (cjstore H mem) lo q lo (map w64 ws)
      (map FMgxaSeamPf.pt_parg args).
Proof.
intros H mem rs ws args f lo q HA HS HU -> Hq.
revert ws HA HS HU. induction args as [|a args IH]; intros ws HA HS HU;
  destruct ws as [|w ws]; [exact I | exact I | destruct HA |].
destruct HA as [Ha HA].
assert (HS' : pf_args_slack ws args) by (destruct a; [exact HS | exact HS | exact (proj2 HS)]).
assert (HU' : forall u, In (AU64 u) args -> 0 <= u < 2 ^ 64) by (intros u Hu; apply HU; right; exact Hu).
cbn [map GXI.args_ok]. split; [|exact (IH ws HA HS' HU')].
destruct a as [v|u|s]; cbn [FMgxaSeamPf.pt_parg GXI.arg_ok].
- destruct Ha as [Hv Hm]. split; [exact Hv|]. rewrite FAM.uw64_mod32. exact Hm.
- cbn [pf_arg_asan] in Ha. subst w. apply FAM.uw64, HU. left. reflexivity.
- destruct HS as [Hsl _].
  destruct Ha as (Hs & Hw & _ & Hb & Hsk & Hd & _ & _ & _).
  pose proof (FAM.str_word w s ltac:(lia) Hsl) as Hw64.
  pose proof (FAM.str_end_bound w s Hsl) as Hend.
  pose proof (FAM.str_slack_length H mem w s) as Hk.
  apply Forall_cons_iff in Hd as [D1 Hd]. apply Forall_cons_iff in Hd as [D2 _].
  unfold zdisjoint in D1, D2. cbn [fst snd] in D1, D2.
  exists (FAM.str_slack H mem w s). rewrite (FAM.uw64 w Hw64). unfold PR.zlength.
  rewrite Hk, FAM.slack_len_eq.
  split; [exact (FAM.str_bytes_of_view H mem w s ltac:(lia) Hend Hb Hsk)|].
  split; [exact Hs|].
  repeat split; lia.
Qed.

End f.
