(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_strlen F_memcpy F_memmove H_str_alloc H_membuffer_assign H_membuffer_append HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition membuffer_append_str_entry := 0x16a10%Z.
Ltac sstep := step; fix_lit_store.

Lemma sseg : forall (lo MB SRC A len cap : Z) (str slack : list byte) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m MB (mbuf_cells A len cap) -> (MB + 32 <= lo \/ bv_unsigned sp <= MB)%Z -> (MB + 32 < 2^64)%Z -> (0 <= len < 2^64)%Z -> (0 < MB)%Z -> (MB mod 8 = 0)%Z ->
  bytes_at rsegs m SRC (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (SRC + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> (0 < SRC)%Z ->
  (SRC + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= SRC)%Z ->
  evt rsegs (fun ms' => exists t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz MB) (wz SRC) (wz (Z.of_nat (length str))) (wz len) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz membuffer_insert_entry) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_append_str_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI MBC MBLO MBHI HL MBNZ MBAL BSRC NONUL PAD S0 SDJ. unfold membuffer_append_str_entry, membuffer_insert_entry. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (word_lt64 sp) as SPB. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB. rewrite length_app in BB. cbn [length] in BB.
  carve_frame 32%nat ST. do 4 sstep. ub_null. zstep. ub_align. zstep. zstep. zstep.
  assert (ES : bv_unsigned (wz SRC) = SRC) by (apply unsigned_lit; lia).
  call strlen_spec. all: rewrite ?ES. all: side (first [exact BSRC | exact NONUL | exact PAD | exact MI | lia]).
  rename MI0 into MI. clear POST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat (split; [eassumption|]). exact ST.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis REALLOCPC : al_realloc_pc L = 0x1995c.
  Notation mown := (mown AI).

  #[using="AC LOK REALLOCPC"] Theorem membuffer_append_str_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (ok : option K) (MB SRC A len cap lo B : Z) (str slack bs : list byte) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 64 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> (0 <= len <= cap)%Z -> (cap + Z.of_nat (length str) + 8 < 2^32)%Z -> mown m LB A cap ok bs ->
    (ok <> None -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0)) ->
    mbloc AI (lb_keep AI ok LB) (bv_unsigned sp) B MB 32 -> (MB mod 8 = 0)%Z ->
    bytes_at rsegs m SRC (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    ((- (SRC + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z -> (0 < SRC)%Z ->
    (SRC + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling \/ bv_unsigned sp <= SRC)%Z ->
    (SRC + Z.of_nat (length str) <= alloc_ceiling)%Z ->
    src_ok AI (lb_keep AI ok LB) (bv_unsigned sp) SRC (Z.of_nat (length str)) str ->
    (SRC + Z.of_nat (length str) <= MB \/ MB + 32 <= SRC)%Z ->
    a0 = wz MB -> a1 = wz SRC ->
    SREACH AI (membuffer_append_post AI ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok MB A len cap (Z.of_nat (length str)) lo B str bs m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_append_str_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI MBC HLC HNC OWN NUL MBL MBAL BSRC NONUL PAD S0 SDJ SHI CR DJS -> ->.
    pose proof (word_lt64 sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BSRC) as BB. rewrite length_app in BB. cbn [length] in BB.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (SUB : forall b, In b (lb_keep AI ok LB) -> In b LB) by (intros b Hb; eapply lb_keep_sub; exact Hb).
    pose proof (mbloc_lo rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL) as MBLO.
    pose proof (mbloc_pos rsegs AI _ _ _ _ _ _ _ _ HR SUB MBL ltac:(lia)) as MBP.
    pose proof (mbloc_errno rsegs AI _ _ _ _ _ _ _ _ LOK HR SUB MBL ltac:(lia)) as MBE.
    assert (MBB : (MB + 32 <= B)%Z).
    { destruct MBL as [H|(b & Hb & H1 & H2)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). cbn in R4. lia. }
    eapply sreach_evt. { eapply (sseg lo MB SRC A len cap str slack); try eassumption; lia. }
    intros ms' P. destruct_exs P. destruct P as (-> & MU1 & WM1 & MI1 & ST1).
    lazymatch type of MI1 with mem_inv _ ?mm => rename mm into m1 end.
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ MBC MU1 WM1 ltac:(cbn; lia)) as MBC1.
    pose proof (bytes_at_transport rsegs _ m m1 _ _ BSRC MU1 ltac:(cbn [disjoint_from]; rewrite length_app; cbn [length]; lia)) as BSRC1.
    apply bytes_at_app in BSRC1. destruct BSRC1 as [BSRC1 _].
    assert (OWN1 : mown m1 LB A cap ok bs).
    { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
      destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4.
      eapply (rw_cells_transport rsegs _ m m1); [exact BLK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. lia. }
    assert (HP1 : hpx AI [(MB, MB + 32)]%Z (lb_keep AI ok LB) (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    eapply sreach_mono.
    { eapply (membuffer_insert_end_spec AI AC LOK REALLOCPC); try eassumption; try reflexivity; lia. }
    intros s' LB' ms'' P. unfold membuffer_append_post in *. destruct_exs P.
    destruct P as (-> & Q1 & Q2 & Q3 & Q4 & HP2 & REST).
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split.
    { eapply (hpx_trans rsegs AI); [exact HP1| exact HP2]. }
    exact REST.
  Qed.
End W.
