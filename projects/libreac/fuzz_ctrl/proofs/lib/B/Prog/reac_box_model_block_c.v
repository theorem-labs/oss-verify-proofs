From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c RcAsanFP.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_MODEL_BLOCK : Z := 0x865d8.
(* K = max(4272, 176 + K(__asan_stack_malloc_0) 208, 240 + max(K(__asan_memset) 2208, K(__asan_memcpy) 2224,
   K(build_dt1_single) 2272, K(name_field) 2240, K(dt1_head) 16)): contracts/libreac/reac_box_model_block.md Names.
   The frame is 160 bytes, A = S - 160 rounded down to 32; the probe writes 8 bytes at A - 4096 >= S - 4272; the
   callees run at A - 64 >= S - 240 (real-stack ASan frame) or at A (side-stack frame); __asan_stack_malloc_0 runs
   at A. *)
Definition REAC_BOX_MODEL_BLOCK_K : Z := 4272.
(* The two 32-byte image blocks that the code copies to o: JOIN_0014 for b = 1, JOIN_0013 for b = 2. *)
Definition JOIN_0013 : Z := 0x21a20.
Definition JOIN_0014 : Z := 0x21a60.

(* The writes outside the side stack (fp's W) and the data ranges (fp's D). *)
Definition reac_box_model_block_W (o S : Z) : list ivl :=
  (S - REAC_BOX_MODEL_BLOCK_K, S) :: (if o =? 0 then [] else [(o, o + 32)]).
Definition reac_box_model_block_D (p o : Z) : list ivl :=
  (if p =? 0 then [] else [(p, p + 296)]) ++ (if o =? 0 then [] else [(o, o + 32)]).

(* The thread cells that fp names are apart from the class-0 side-stack bytes (struct.asan.runtime RT4.3) and from
   the shadow of the function's own window [lo, hi): the function's own frame on the side stack or on the real stack
   keeps them. *)
Definition reac_box_model_block_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [0%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The asan writes beyond the plain ones: the class-0 side-stack bytes and the shadow of the window. *)
Definition reac_box_model_block_X (S FS : Z) : list ivl :=
  fp_w [0%nat] FS ++ [(shadow_addr (S - REAC_BOX_MODEL_BLOCK_K), shadow_addr S)].

(* The ubsan post (lib/U/Prog/reac_box_model_block_c.v, the plain form) with K = 4272, the writes of
   reac_box_model_block_X, and the asan state at the return. *)
Definition reac_box_model_block_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb : list byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if (p =? 0) || (o =? 0) then -1 else rc row b))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ (if (p =? 0) || (o =? 0)
        then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                    reac_box_model_block_X (bv_unsigned sp) FS) m m'
        else bytes_at rsegs m' o (synth row b nb) /\
             munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                    reac_box_model_block_X (bv_unsigned sp) FS) m m')
    /\ wmono rsegs m m'
    /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
    /\ asan_cells m' /\ shadow_rw m'
    /\ addressable m' (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K
    /\ fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
         (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o)
    /\ reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).

(* The ubsan contract (lib/U/Prog/reac_box_model_block_c.v) with K = 4272, o apart from both JOIN blocks, and the
   premises of the asan-ubsan build (S1.2, S1.6, S1.7 of the English contract): the runtime's cells and shadow
   (asan_cells, shadow_rw), the window in AppMem and addressable, the addressable bytes at m, the name, o and the JOIN
   block that b selects, o's end in AppMem and o apart from the runtime's cells, and the side-stack state for
   __asan_stack_malloc_0 (fp [0%nat], the name apart from fp_w [0%nat] FS, reac_box_model_block_tls). The same
   premises give those of dt1_head and name_field (lib/B/Prog/dt1_head_c.v, name_field_c.v). *)
Definition reac_box_model_block_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb ob : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 o ->
    0 <= p < 2^64 -> 0 <= b < 2^64 -> 0 <= o < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
               (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               name_ok nb /\ bytes_at rsegs m (rname row) nb /\
               (bv_unsigned sp <= rname row \/
                rname row + Z.of_nat (length nb) <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
               (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    (p <> 0 -> addressable m p 296) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               addressable m (rname row) (Z.of_nat (length nb))) ->
    (o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
    reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    evt rsegs
      (reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).

(* --------------------------------------------------------------------------------------------------------- *)
(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery), a Theorem Labs lane's rewalk-F-policy.md (a working note, not in this delivery) canonical shape): the same run as
   an ExecF.evtF under a universally quantified footprint RNG (bound first), with the premises of
   reac_box_model_block_contract unchanged and one rng premise per region the run reads or writes (instruction
   fetch is not an access), each under the guard its data premise carries.  The regions come from the steps of the
   run (lib/B/Prog/reac_box_model_block.v, _body.v, _case*.v) and from the footprint forms of the callees
   __asan_stack_malloc_0, __asan_memset, __asan_memcpy, build_dt1_single, dt1_head and name_field.  The side stack
   and the thread cells take the narrow form of the B reac_ctrl_parse text (a working branch d0b3606c9c9
   lib/B/Prog/reac_ctrl_parse_c.v) at class 0.  The footprint forms of __asan_memcpy and __asan_memset this proof
   applies (a working branch 9869f1d1f86) take RngBytes.rng_bytes RNG, so this statement
   takes it too.

     image (code, jump table, JOIN, GOT, the     [0x10000, 0x5fe000)                 read/write
       runtime words [RT_LO, RT_HI))
     own window (frame, spills, probe, callees)  [S - K, S)                          read/write
     window shadow (frame words, callee checks)  8-aligned cover of its shadow       read/write, checked
     side-stack header (hint, flags)             [FS, fs_frame FS 0 0)               read/write
     class-0 side-stack bytes                    fp_w [0%nat] FS                     read/write
     the thread cells asan_tls_cells names       fp_tls                              read
     the row (p <> 0)                            [p + 16, p + 291)                   read, checked
     the out block (p <> 0, o <> 0)              [o, o + 32)                         read/write, checked
     JOIN_0014 (b = 1) / JOIN_0013 (b = 2)       shadow of [JOIN, JOIN + 32)         read
     the name (b = 5, 6, has row, rname row)     [rname row, + length nb)            read, checked

   Each checked region also carries the 8-ALIGNED shadow word cover (sh_cover) its instrumented checks load: the
   check of a field is a load of the shadow byte at (a >> 3) + ASAN_K and a compare, and __asan_memcpy's and
   __asan_memset's quick check loads aligned shadow words.  The JOIN blocks themselves are inside the image range.
   reac_box_model_block_contract_of_F gives the old statement back at ExecF.RNG_all. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.

(* The 8-aligned shadow word cover of [a, a + n) with n > 0 (a Theorem Labs lane's canonical form). *)
Definition sh_cover (RNG : ExecF.footprint) (a n : Z) : Prop :=
  ExecF.rng RNG (shadow_addr a / 8 * 8) (shadow_addr (a + n - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8).

Definition reac_box_model_block_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p b o FS : Z) (row nb ob : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 o ->
    0 <= p < 2^64 -> 0 <= b < 2^64 -> 0 <= o < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
               (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               name_ok nb /\ bytes_at rsegs m (rname row) nb /\
               (bv_unsigned sp <= rname row \/
                rname row + Z.of_nat (length nb) <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o)) ->
    (o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
               (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) /\
               (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o)) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    (p <> 0 -> addressable m p 296) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               addressable m (rname row) (Z.of_nat (length nb))) ->
    (o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp)
      (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
               fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS)) ->
    reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (* the footprint is byte-wise (the callees __asan_memcpy / __asan_memset carry it), then the regions the run
       reads or writes *)
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    sh_cover RNG (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K ->
    ExecF.rng RNG FS (fs_frame FS 0%nat 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    (p <> 0 -> ExecF.rng RNG (p + 16) 275 /\ sh_cover RNG (p + 16) 275) ->
    (p <> 0 -> o <> 0 -> ExecF.rng RNG o 32 /\ sh_cover RNG o 32) ->
    (b = 1 -> sh_cover RNG JOIN_0014 32) ->
    (b = 2 -> sh_cover RNG JOIN_0013 32) ->
    (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
       ExecF.rng RNG (rname row) (Z.of_nat (length nb)) /\ sh_cover RNG (rname row) (Z.of_nat (length nb))) ->
    ExecF.evtF rsegs RNG
      (reac_box_model_block_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m (seg_rom rsegs)).

(* RECIPE step 1: the old statement as a corollary of the footprint form at ExecF.RNG_all, every rng premise by
   ExecF.rng_all from the bounds the old premises carry: the image is a literal, the window is below APPMEM_END,
   the side stack is in the application memory by fs_place, the cells of asan_tls_cells by their bytes_at bounds,
   the row, o, the JOIN blocks and the name by addressable, and a shadow address is below APPMEM_END / 8 + ASAN_K.
   reac_box_model_block_holdsF.v proves reac_box_model_block_contract_F; the old reac_box_model_block_contract
   follows from it by this lemma. *)
Lemma reac_box_model_block_contract_of_F :
  reac_box_model_block_contract_F -> reac_box_model_block_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p b o FS row nb ob E0 E1 E2 Rp Rb Ro Hal ST HP HN HO MI AC SW HHM HAE AW APR ANM AO AJ4 AJ3 FP0 HDJ TLS0.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold HIGHMEM_BEG, APPMEM_END, REAC_BOX_MODEL_BLOCK_K in HHM', HAE'.
  (* the side stack is inside the application memory *)
  pose proof FP0 as (DT & TS & C & T & DB & k & HTC & HTP & HPL & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
  pose proof HPL as (PL0 & PL1 & PL2 & PL3 & PL4).
  assert (FSlo : 0 <= FS) by lia.
  assert (FShi : FS + FS_SIZE <= 2^64).
  { pose proof (PL3 FS ltac:(unfold FS_SIZE; lia)) as A1.
    pose proof (PL3 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2. lia. }
  unfold FS_SIZE in FShi.
  assert (EM : fs_M 0 = 16384) by reflexivity.
  assert (E0F : forall j, fs_frame FS 0 j = FS + 36864 + j * 64)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 0) with 0; lia).
  assert (EF : fs_flag FS 0 0 = FS + 4096)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 0)) with 32768; lia).
  assert (EH : fs_hint FS 0 = FS) by (unfold fs_hint; change (Z.of_nat 0) with 0; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            t3 t4 t5 t6 F fc m p b o FS row nb ob); try assumption; unfold sh_cover, shadow_addr, ASAN_K.
  - (* rng_bytes *) intros bb jj _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; lia.
  - (* window *) apply ExecF.rng_all; unfold REAC_BOX_MODEL_BLOCK_K; lia.
  - apply ExecF.rng_all; unfold REAC_BOX_MODEL_BLOCK_K; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0F; lia.
  - (* class-0 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E0F, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the cells of asan_tls_cells *)
    intros DT' TS' C' T' DB' k' Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
  - (* the row *) intros Hp. destruct (APR Hp) as (AP0 & AP1 & AP2 & AP3). unfold APPMEM_END in AP2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - (* o *) intros Hp Hoz. destruct (AO Hoz) as ((AO0 & AO1 & AO2 & AO3) & _ & _). unfold APPMEM_END in AO2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - (* JOIN_0014 *) intros _. apply ExecF.rng_all; unfold JOIN_0014; Z.div_mod_to_equations; lia.
  - (* JOIN_0013 *) intros _. apply ExecF.rng_all; unfold JOIN_0013; Z.div_mod_to_equations; lia.
  - (* the name *) intros Hp Hb Hh Hr. destruct (ANM Hp Hb Hh Hr) as (AN0 & AN1 & AN2 & AN3).
    unfold APPMEM_END in AN2. split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
Qed.
