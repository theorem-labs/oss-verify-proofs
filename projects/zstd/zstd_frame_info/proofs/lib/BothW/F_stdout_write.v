(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_syscalls F_stdio_write StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
  file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.

Definition STDOUT_WRITE_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac exact_frm := lazymatch goal with |- frm0 ?f => first [is_evar f; fail 1 "exact_frm: evar" | assumption] end.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].


(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma rw_cells_recast : forall m A cs cs',
  rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells bsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
#[using="Type"] Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells bsegs m A (pre ++ C4 a :: post) -> rw_cells bsegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
End CANSEC2.
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells bsegs m A (C4 v :: cs) -> rw_cells bsegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
#[using="Type"] Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.

#[using="Type"] Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). Local Ltac2 Set LiaHints.tbl := fun () => "0010=63374621462.3000001S".
rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells bsegs m A (CB 4 (le4 v) :: cs) -> rw_cells bsegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.

Section StdoutWrite.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.

  (* [comment removed for export] *)
  Definition so_after (so : stdout_st) : stdout_st :=
    mkStdout true [] (if so_first so then false else so_lbf_nl so) false.

  Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
      /\ ssp_cells m' canary
      /\ st' = set_so (so_after (get_so st)) st.

  #[using="get_set set_set"] Lemma stdout_writefn_spec :
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      let so := get_so st in
      so_active so = true ->
      rw_cells bsegs m RSTDOUT (stdout_cells so flags mode tail) ->
      Z.land (bv_unsigned flags) 64 = 0 ->
      bytes_at bsegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
      bytes_at bsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (0x5f6000 <= lo) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      (bv_unsigned sp < 2^47) -> (S + zlength s <= 2^47) ->          (* [comment removed for export] *)
      implAM RNG (stdout_writefn get_so set_so s) st
            (stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom bsegs)).
  Proof.
    intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI S0 Shi SEPS RSTK RS RIMG SP47 S47.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. change bsegs with bsegs in GOT, GUARD. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
    assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
    unfold stdout_writefn. apply implAM_rdso.
    unfold stdout_cells, wfn_of, lbf_of in *.
    destruct (so_first (get_so st)) eqn:FIRST.
    - (* [comment removed for export] *)
      apply implAM_bind_assoc. apply implAM_updso. apply implAM_bind_assoc.
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      pose proof (wmono_refl bsegs m) as WM.
      (apply implAM_sysk; [exact I|]).
      change (bytes_at bsegs m S (to_bytes s)) with (boxed (bytes_at bsegs m S (to_bytes s))) in SRC.
      change (bytes_at bsegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at bsegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
      Local Ltac2 Set LiaHints.tbl := fun () => "01j0?10964954211.72 10966888420.81 11716686062.81 15525371630.81 17221588796.81 18090682944.81 18092878279.72 18502038852.88 18926697116.72 18928695579.81 19006120615.84 19246642144.77 19612710337.93 22058496219.72 22060692316.81 22154903132.81 22157098459.72 23230285244.83 24440526862.81 24442723209.72 24812739566.84 25071629079.81 25071629079.83 25071629079.84 25071629079.88 25071629079.93 25080086061.10325181144806.93 25566553219.11225566553219.84 26506338798.84 28044327893.82 28786468985.72 28788403198.81 29572283170.72 31575836224.72 31578097095.81 31995378610.81 32780138878.72 32782400249.81 33595931868.72 33680001082.81 34290115814.75 38806986883.11138806986883.81 39813346096.10239941652002.10440259163999.81 40271167661.81 41562522430.10341688470069.81 41690403250.72 41996913241.72 42149039858.81 42151038325.72 43061773371.73 43734661222.88 43987951407.11143987951407.83 44190155057.88 44510485275.81 44512745628.72 44713017681.82 4498443158.104 45221239098.84 47073752772.93 47727670330.81 47729670077.72 48781039854.81 50052274856.81 50096175936.72 50280742294.81 51359702632.81 51361635823.72 5180980284.84  52155062597.73 5231358608.81  5233619223.72  53767577772.82 53767577775.11153860909166.83 54618151079.83 55104759171.11255104759171.83 55214427825.93 56172318510.81 563227834.83   57288667037.81 57622410744.10557622410744.95 57652511122.81 57654444565.72 57677589369.81 57679587582.72 59028845166.83 59310682963.81 60300506080.77 60922667730.81 60924666197.72 6138222720.72  6140418823.81  6166287527.81  61874979822.84 63138427969.88 63235321900.11063235321901.80 64303108851.79 64303108851.81 64305041780.72 64318189174.77 64616299737.77 64650279534.83 64660241775.82 64662437608.73 7186541364.102 7190913411.81  8416990054.88  8529237941.81  911097830.93   9279251259.81  9911485211.81  9913745564.72  00000100200B00R00^00_00`00i01201;01D01M01]01f01o02802A02M02Z02g03703@03I03R03[03d04404=04F04O04_05905F05S05T05f06806M06N06O06]06k07407=07F07O07[07i07j08308<08E08F08S08`08l09509A09M09V09_09h0:40:=0:K0:T0:U0:V0:f0;20;>0;?0;@0;A0;M0;Y0;Z0;[0;g0<30<C0<L0<U0<^0<g0=00=>0=?0=J0=U0=^0=g0=h0=i0>90>I0>R0>`0>n0?;0?H0?Q0?a0@10@=0@I0@U0@a0@m0A60A?0AO0A[0Ag0B<0BQ0BZ0B[0Bd0C00C90CBFFS2LO3GLO3LSB3LBBS2LO3GLO3LSB3LBBS3LSB3LBB2HBFFS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS2LO3GLO3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBB2HBS3S473LSB3LBBS3S473LSB3LBBS2LO3GLO3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS2LO3GLO3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS2LO3GLO3LSB3LBBS2LO3GLO4SEP14SEP23LSB3LBBS3Shi3LSB3LBBS3Shi3LSB3LBBFS4BUFL3GLO3LSB3LBBS4BUFL3GLO3LSB3LBBS4BUFL2LO3GLO3LSB3LBBFFS4SP473LSB3LBBS4SP473LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS2LO3LSB3LBBS4SP473LSB3LBBFS3LSB3LBBS3LSB3LBBS3LSB3LBBFS3GLO3LSB3LBBS3GLO3LSB3LBBS2LO3LSB3LBBS3LSB3LBBS2LO3LSB3LBBS2LO3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS2S13LSB3LBBS3LSB3LBBS4SP473LSB3LBBS3LSB3LBBFFS2LO3GLO3LSB3LBBS2LO3LSB3LBBS2LO3LSB3LBBFFFS3LSB3LBB2HBS2S13LSB3LBBFFS2LO3LSB3LBBS2LO3LSB3LBBS2LO3GLO3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS3LSB3LBBS4SP473LSB3LBBFS3LSB3LBB1HS3LSB3LBB1HS3LSB3LBBS3LSB3LBBFFS2LO3GLO3LSB3LBBS3LSB3LBB2He3He0S3LSB3LBBS4BUFL3LSB3LBBS4BUFL3LSB3LBBS3GLO3LSB3LBBS3GLO3LSB3LBBS3LSB3LBBS2LO3GLO3LSB3LBBS2LO3GLO3LSB3LBBS2LO3LSB3LBBS2LO3LSB3LBBS2S03LSB3LBBS2S03LSB3LBBS2S03LSB3LBBS3LSB3LBBS3LSB3LBBS2LO3GLO3LSB3LBBS2S23LSB3LBBS2S23LSB3LBBS2LO3GLO4SP473LSB3LBBS2LO3GLO4SP473LSB3LBBS3LSB3LBBFS3LSB3LBBS3LSB3LBB2HeS3LSB3LBBS3LSB3LBB".
carve_frame 32%nat ST.
      do 9 step. rewrite firstn1_le4, zext_extract_le1. unfold zx8.
      step. step. step. fix_lit_store. step.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
      do 10 step. step_ecall.
      replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply sx32_small; lia).
      split. { at_nodeA_red. split; [| exact I]. split_spine; try reflexivity; try lia. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0. cbv iota.
      apply implAM_updso.
      (* [comment removed for export] *)
      apply implAM_from_evt. sys_nret.
      do 5 step.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      step. step.
      fix_lbf FC.
      step. apply evtF_done.
      rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
      unfold stdout_stdio_write. apply (implAM_rdso get_so). rewrite get_set. cbn [so_buf].
      apply rw_cells_CB4_C4 in FC.
      eapply implAM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH; lia | unfold GLOBALS_TOP; lia | unfold got_ssp; lia | unfold ssp_guard; lia
                   | unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
                   | destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
                   | right; unfold zlength in BUFL |- *; split; lia
                   | src_now SRC SEPS MU LSB
                   | exact RS | exact RIMG
                   | unfold STDIO_WRITE_DEPTH, GLOBALS_TOP in *; unfold zlength in BUFL |- *; solve_rng ]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite !unsigned_lit in MU2, ST2 by lia.
      apply implAM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 0x8eac0)) with (Z_to_bv 64 0x8eac0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct SSP2 as [GOT2 GUARD2]. change bsegs with bsegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
      assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport bsegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
      step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + apply (munch_trans _ m m0 m2).
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + eapply wmono_trans; [exact WM | exact WM2].
      + split; [exact GOT2 | exact GUARD2].
      + rewrite ?set_set. reflexivity.
    - (* [comment removed for export] *)
      apply implAM_retb. unfold stdout_stdio_write. apply (implAM_rdso get_so).
      pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
      assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
      eapply implAM_bind.
      { eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
          (lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
          (flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
        all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | split; [exact GOT | exact GUARD]
                   | lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold GLOBALS_TOP; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
        all: first [ destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
                   | right; unfold zlength in BUFL |- *; split; lia
                   | exact RS | exact RIMG
                   | unfold STDIO_WRITE_DEPTH, GLOBALS_TOP in *; unfold zlength in BUFL |- *; solve_rng ]. }
      cbv beta. intros [] st' ms' PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      apply implAM_upd. apply evtF_done. rewrite ?get_set.
      unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
      sys_finish.
      + eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
      + rewrite ?set_set. reflexivity.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End StdoutWrite.
End CANSEC3.
