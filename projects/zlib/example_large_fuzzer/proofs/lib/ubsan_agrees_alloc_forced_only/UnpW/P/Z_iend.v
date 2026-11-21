(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTarget. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZApi ZHarness. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Layout Drv_kit F_fwrite Z_kit Zlib_iface Zh_kit Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_irep Z_ikit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState RefInflateSafeD RefInflateSafeTY ZApiInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition PC_IE_RET1 : Z := 0x1f218.     (* [comment removed for export] *)
Definition PC_IE_RET2 : Z := 0x1f230.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ie_at_free (S lo ret ptr : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz ret) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz S) s1 a0 (wz ptr) a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz Z_ZCFREE) fc None m' (seg_rom psegs)
    /\ rw_cells psegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ stk psegs m' lo (bv_unsigned sp + -16)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'.

(* [comment removed for export] *)
Lemma iend_to_free : forall (L : ilay) (s : inflate_state) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x5c000 <= lo ->
  rw_cells psegs m (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) -> isA m L s ->
  bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 -> 0 < il_As L -> il_As L + 7176 <= lo ->
  16180 <= is_mode s <= 16211 -> (is_window_blk s <> None -> 0 < il_Aw L < 2^63) ->
  mem_inv psegs m ->
  evt psegs (ie_at_free (il_S L) lo (if is_window_blk s then PC_IE_RET1 else PC_IE_RET2) (if is_window_blk s then il_Aw L else il_As L)
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (il_S L)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_INFLATEEND) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros STK LO1 LO2 ZQ GA SPS S63 As0 As1 RM RW MI.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in ZQ. open_isA GA.
  unfold Z_INFLATEEND. carve_frame 16%nat STK.
  do 3 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_false. do 2 zs. br_true.
  do 4 zs. rewrite (swrap32_sub _ 16180) by (try reflexivity; lia). do 2 zs. br_false.
  do 4 zs.
  destruct (is_window_blk s) as [wb|] eqn:EW; cbn [win_addr].
  - specialize (RW ltac:(discriminate)). zs. br_false. do 4 zs.
    apply evt_done. unfold ie_at_free. do 15 eexists. split; [reflexivity|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  - zs. br_true. do 3 zs.
    apply evt_done. unfold ie_at_free. do 15 eexists. split; [reflexivity|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

(* [comment removed for export] *)
Lemma iend_to_free2 : forall (L : ilay) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk psegs m lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 32 -> 0x5c000 <= lo ->
  rw_cells psegs m (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
  bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
               ms' = MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 (wz (il_As L)) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz Z_ZCFREE) fc None m (seg_rom psegs))
    (MS (mkR (wz PC_IE_RET1) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_IE_RET1) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZQ SPS S63 MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in ZQ.
  unfold PC_IE_RET1. do 6 zs.
  apply evt_done. do 14 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iend_tail : forall (L : ilay) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word) (lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells psegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> stk psegs m lo (bv_unsigned sp + -16) -> lo <= bv_unsigned sp - 32 -> 0x5c000 <= lo ->
  rw_cells psegs m (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
  bv_unsigned sp <= il_S L -> il_S L + 112 < 2^63 ->
  mem_inv psegs m ->
  evt psegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom psegs)
               /\ munch [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
               /\ exists j, rw_cells psegs m' (il_S L + 48) [CB 64 j])
    (MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_IE_RET2) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros FR STK LO1 LO2 ZQ SPS S63 MI.
  pose proof (munch_refl [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold izs_priv_cells, Z_ZCALLOC, Z_ZCFREE in ZQ.
  unfold PC_IE_RET2. do 5 zs.
  release_frame FR STK (bv_unsigned sp).
  zs.
  apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  destruct (rw_cells_forget psegs _ _ _ ZQ) as (j & Hj). exists j. exact Hj.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZFREE.
  Hypothesis FREE : rfree_stmt.

  Lemma izfree : forall {A : Type} (K : unit -> Monad.M PState A) (POST : A -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (p : bptr) (Ab n lo B : Z) (errv : word),
    RHEAP s LBc m -> In (p, Ab, n) LBc ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz Ab ->
    (forall (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv] -> rauxv_ok m' B ->
       rheap_pres (lb_remove p LBc) (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       RHEAP s' (lb_remove p LBc) m' ->
       implM psegs (K tt) s' POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (bind lops (lib_free lops (Some p)) K) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP HIN AUX SPB STK CEIL LOSP ERRC MI TP -> KONT.
    cbn [bind lops Target.ops lib_free].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCFREE. zstep. zstep. apply evt_done.
    lazymatch goal with |- ITree.impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_bind.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc p Ab n lo B errv);
        [ exact HP | exact HIN | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity ]. }
    cbv beta. intros [] s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
    exact (KONT s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MI' ST' ERR' AUX' HPR' EFA' ESO' HP').
  Qed.

  Lemma izfree_last : forall (POST : unit -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (p : bptr) (Ab n lo B : Z) (errv : word),
    RHEAP s LBc m -> In (p, Ab, n) LBc ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz Ab ->
    (forall (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv] -> rauxv_ok m' B ->
       rheap_pres (lb_remove p LBc) (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       RHEAP s' (lb_remove p LBc) m' ->
       evt psegs (POST tt s')
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (lib_free lops (Some p)) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP HIN AUX SPB STK CEIL LOSP ERRC MI TP -> KONT.
    cbn [lops Target.ops lib_free].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCFREE. zstep. zstep. apply evt_done.
    lazymatch goal with |- ITree.impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_post_evt''.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc p Ab n lo B errv);
        [ exact HP | exact HIN | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity ]. }
    intros [] s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
    exact (KONT s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MI' ST' ERR' AUX' HPR' EFA' ESO' HP').
  Qed.
End ZFREE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iblocks_inv' : forall (w w' : option bptr) Aw Aw' (sp_ sp' : bptr) As As',
  Zlib_iface.iblocks w Aw sp_ As = iblk_list w' Aw' sp' As' -> w' = w /\ sp' = sp_ /\ As' = As /\ (w <> None -> Aw' = Aw).
Proof.
  intros w w' Aw Aw' sp_ sp' As As'. unfold Zlib_iface.iblocks, iblk_list, the_zapi. cbn [z_wsize z_isize zinst].
  destruct w as [wp|]; destruct w' as [wp'|]; cbn [app]; intros E; try discriminate E.
  - injection E as E1 E2 E3 E4. subst. repeat split; reflexivity.
  - injection E as E1 E2. subst. repeat split; try reflexivity. intros NE. exfalso. apply NE. reflexivity.
Qed.

Section IEND.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.

  (* [comment removed for export] *)
  Lemma iend_second : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
      (s st1 : PState) (LB : list block) (L : ilay) (sp_ : bptr) (lo B : Z) (errv1 canary : word)
      (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word)
      (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    lx_env m1 st1 [(sp_, il_As L, 7176)] LB (wz (bv_unsigned sp + -16)) tp B lo errv1 canary ->
    rw_cells psegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells psegs m1 (il_S L) (zs_pub ni ai ti no ao to p1 p2) ->
    rw_cells psegs m1 (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
    lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m1 -> ps_so st1 = ps_so s -> ps_fa st1 = ps_fa s ->
    strm_in_frame sp (il_S L) B -> lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> frm0 fc ->
    implM psegs (lib_free lops (Some sp_)) st1
      (inflateEnd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (il_S L) lo B canary m)
      (MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 (wz (il_As L)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m1 (seg_rom psegs)).
  Proof.
    intros until t6. intros ENV1 FR PUB ZQ PRES1 ESO1 EFA1 SIF LOSP FRM0.
    pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & B63 & ST1 & LOC1 & LOG1 & ERR1 & TP1 & MI1).
    destruct SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. unfold Z_INFLATEEND_STACK, RFREE_STACK in LOSP. unfold GLOBALS_TOP in LOG1.
    pose proof alloc_ceiling_range as CR.
    assert (E16 : bv_unsigned (wz (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    eapply (izfree_last FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 _ sp_ (il_As L) 7176 lo B errv1);
      [ exact HP1 | left; reflexivity | exact AUX1 | exact SPB1 | exact ST1 | exact LOC1 | rewrite E16; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
      | exact TP1 | reflexivity | ].
    intros st2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MI2 ST2 ERR2 AUX2 HPR2 EFA2 ESO2 HP2.
    cbn [app] in HPR2, HP2. rewrite (lb_remove_head sp_ _ _ _ (HND _ _ _ HP1)) in HPR2, HP2. rewrite E16 in HPR2, ST2.
    assert (ENV2 : lx_env m2 st2 [] LB (wz (bv_unsigned sp + -16)) tp B lo errv1 canary).
    { eapply (lx_env_heap m1 m2 st1 st2); [exact ENV1| rewrite E16; exact HPR2| exact HP2| exact MI2| rewrite E16; exact ST2| exact ERR2| exact AUX2]. }
    assert (AGC : forall A0 n, bv_unsigned sp + -16 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3 a Ha. apply HPR2; [lia|]. left. lia. }
    apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in PUB; [|apply AGC; unfold zs_pub; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in ZQ; [|apply AGC; unfold izs_priv_cells; cbn [cells_size csize Nat.add]; lia].
    replace (ret_pc (wz PC_IE_RET2)) with (wz PC_IE_RET2) by (symmetry; apply ret_pc_even; [unfold PC_IE_RET2; lia| reflexivity]).
    eapply evt_mono; [exact (iend_tail L msg adler dt p3 resv lo ra sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                                FR ST2 ltac:(lia) ltac:(lia) ZQ SF1 ltac:(lia) MI2)|].
    intros ms' (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & STK' & (j & ZQ')).
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= lo /\ 0 < blk_addr b).
    { intros b Hb. pose proof (HBR _ _ _ b HP2 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    unfold inflateEnd_post. exists v0, v1, v2, (wz 0), c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, F, fc, m'.
    split; [reflexivity|]. split; [|split].
    - unfold lx_post_env. split.
      { exists errv1. eapply (lx_env_munch [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m2 m' st2 [] LB (wz (bv_unsigned sp + -16)) sp tp B lo errv1 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
        - constructor; [|constructor; [|constructor]]; unfold rclient_write_ok; cbn [fst snd]; left; lia.
        - intros a Ha. cbn [outside]. repeat split; lia. }
      split; [exact FRM0|]. split; [|split; congruence].
      eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans.
      { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| auto]. }
      apply (lx_pres_of_munch LB (bv_unsigned sp) _ _ m2 m' MU' WM').
      intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia.
    - unfold wint, Z_OK. reflexivity.
    - apply (rw_cells_transport psegs [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m2 m') in PUB; [| exact MU'| exact WM'| unfold zs_pub; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
      assert (HJ : rw_cells psegs m' (il_S L) (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j])).
      { apply rw_cells_app. split; [exact PUB|]. unfold zs_pub. cbn [cells_size csize Nat.add]. exact ZQ'. }
      destruct (rw_cells_forget psegs m' _ _ HJ) as (j' & Hj'). exists j'. exact Hj'.
  Qed.

  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.

  Theorem inflateEnd_ok : inflateEnd_stmt R.
  Proof.
    unfold inflateEnd_stmt. intros until canary. intros ENV PUB ZR HEND SIF LOSP SP16 FRM0 ->.
    rewrite ER in ZR. destruct ZR as (s_a & L & w' & sp' & ES & EL & HW & [HZQ HIST] & HI & HA & HPq).
    destruct (iblocks_inv' _ _ _ _ _ _ _ _ EL) as (-> & -> & EAs & EAw). subst S.
    destruct HZQ as (dt & p3 & resv & ZQ). destruct HIST as [GA GT Gl Gw Gc Gwin ARRS LAY].
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & STK & LOC & LOG & ERR & TP & MI).
    pose proof SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. pose proof LOSP as LOSP'. unfold Z_INFLATEEND_STACK, RFREE_STACK in LOSP'. unfold GLOBALS_TOP in LOG.
    pose proof alloc_ceiling_range as CR.
    destruct HI as (_ & _ & HINV & _). destruct HINV as (_ & _ & HMF).
    pose proof (RefInflateSafeS2.MF_mode_range _ _ _ _ HMF) as RM. unfold HEAD, MEM, SYNC in RM.
    assert (RB : forall b, In b (Zlib_iface.iblocks w Aw sp_ As ++ LB) -> 0 < blk_addr b /\ blk_addr b + blk_size b <= lo).
    { intros b Hb. pose proof (HBR _ _ _ b HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    assert (RAs : 0 < il_As L /\ il_As L + 7176 <= lo).
    { rewrite EAs. apply (RB (sp_, As, 7176)). apply in_or_app. left. unfold Zlib_iface.iblocks. apply in_or_app. right. left. reflexivity. }
    assert (RW : is_window_blk s_a <> None -> 0 < il_Aw L < 2 ^ 63).
    { intros NE. destruct w as [wp|]; [|exfalso; apply NE; apply HW; reflexivity].
      rewrite (EAw ltac:(discriminate)). pose proof (RB (wp, Aw, 32768) ltac:(apply in_or_app; left; left; reflexivity)) as Q. cbn [blk_addr blk_size fst snd] in Q. lia. }
    assert (E16 : bv_unsigned (wz (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    eapply implM_evt; [exact (iend_to_free L s_a (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv lo ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               STK ltac:(lia) ltac:(lia) ZQ GA SF1 ltac:(lia) (proj1 RAs) (proj2 RAs) ltac:(lia) RW MI)|].
    intros ms1 (t0' & t1' & t2' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & FR & STK1 & MU1 & WM1 & MI1).
    assert (ENV1 : lx_env m1 s (Zlib_iface.iblocks w Aw sp_ As) LB (wz (bv_unsigned sp + -16)) tp B lo errv canary).
    { eapply (lx_env_munch [(lo, bv_unsigned sp)] m m1 s _ LB sp (wz (bv_unsigned sp + -16)) tp B lo errv canary HFRAME ENV MU1 WM1 MI1);
        [rewrite E16; exact STK1| rewrite E16; lia| |].
      - constructor; [|constructor]. unfold rclient_write_ok; cbn [fst snd]; left; lia.
      - intros a Ha. cbn [outside]. repeat split; lia. }
    apply (rw_cells_transport psegs [(lo, bv_unsigned sp)] m m1) in PUB; [| exact MU1| exact WM1| unfold zs_pub; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
    apply (rw_cells_transport psegs [(lo, bv_unsigned sp)] m m1) in ZQ; [| exact MU1| exact WM1| unfold izs_priv_cells; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m1).
    { apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp)] m m1 MU1 WM1).
      intros a (NX & HC). cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (RB b ltac:(apply in_or_app; right; exact Hb))|]; repeat split; lia. }
    destruct w as [wp|].
    - (* [comment removed for export] *)
      destruct (is_window_blk s_a) as [wb|] eqn:EW; [|exfalso; pose proof (proj2 HW eq_refl) as Q; discriminate Q].
      rewrite (EAw ltac:(discriminate)) in *.
      pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & ST1 & LOC1 & _ & ERR1 & TP1 & _).
      eapply (izfree FREE (fun _ => lib_free lops (Some sp_)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s _ wp Aw 32768 lo B errv);
        [ exact HP1 | left; reflexivity | exact AUX1 | exact SPB1 | exact ST1 | exact LOC1 | rewrite E16; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
        | exact TP1 | reflexivity | ].
      intros st2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MI2 ST2 ERR2 AUX2 HPR2 EFA2 ESO2 HP2.
      unfold Zlib_iface.iblocks, the_zapi in HPR2, HP2, HP1. cbn [z_wsize z_isize zinst app] in HPR2, HP2, HP1.
      rewrite (lb_remove_head wp _ _ _ (HND _ _ _ HP1)) in HPR2, HP2. rewrite E16 in HPR2, ST2.
      assert (ENV2 : lx_env m2 st2 [(sp_, il_As L, 7176)] LB (wz (bv_unsigned sp + -16)) tp B lo errv canary).
      { eapply (lx_env_heap m1 m2 s st2); [exact ENV1| rewrite E16; eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; right; exact Hb]| rewrite EAs; exact HP2| exact MI2
          | rewrite E16; exact ST2| exact ERR2| exact AUX2]. }
      assert (AGC : forall A0 n, bv_unsigned sp + -16 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
      { intros A0 n H1 H2 H3 a Ha. apply HPR2; [lia|]. left. lia. }
      apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
      apply (Z_dview.rw_cells_agree m1 m2) in PUB; [|apply AGC; unfold zs_pub; cbn [cells_size csize Nat.add]; lia].
      apply (Z_dview.rw_cells_agree m1 m2) in ZQ; [|apply AGC; unfold izs_priv_cells; cbn [cells_size csize Nat.add]; lia].
      assert (PRES2 : lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; right; exact Hb]. }
      replace (ret_pc (wz PC_IE_RET1)) with (wz PC_IE_RET1) by (symmetry; apply ret_pc_even; [unfold PC_IE_RET1; lia| reflexivity]).
      eapply implM_evt; [exact (iend_to_free2 L (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv lo ra sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                                 FR ST2 ltac:(lia) ltac:(lia) ZQ SF1 ltac:(lia) MI2)|].
      intros ms3 (v0 & v1 & v2 & c0 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->).
      exact (iend_second ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m2 s st2 LB L sp_ lo B errv canary ni ai ti no ao to p1 p2
               (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv v0 v1 v2 c0 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6
               ENV2 FR PUB ZQ PRES2 ESO2 EFA2 SIF LOSP FRM0).
    - (* [comment removed for export] *)
      destruct (is_window_blk s_a) as [wb|] eqn:EW; [exfalso; pose proof (proj1 HW eq_refl) as Q; discriminate Q|].
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      rewrite <- EAs in ENV1.
      exact (iend_second ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s s LB L sp_ lo B errv canary ni ai ti no ao to p1 p2
               (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
               ENV1 FR PUB ZQ PRES1 eq_refl eq_refl SIF LOSP FRM0).
  Qed.
End IEND.
End WithCeiling0.
