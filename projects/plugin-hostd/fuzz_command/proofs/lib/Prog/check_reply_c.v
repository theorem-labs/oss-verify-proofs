From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandFP printf_facts_c
  sup_reply_code_c rec_code_declared_c rec_shape_of_c check_reply_answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_REPLY : Z := 0x14404.
Definition CHECK_REPLY_K : Z := 6000.

Fixpoint upto0 (l : list byte) : list byte :=
  match l with
  | [] => []
  | b :: l' => if bv_unsigned b =? 0 then [] else b :: upto0 l'
  end.

Definition img_str (A : Z) : list byte :=
  match image_bytes rsegs A 128 with Some bs => upto0 bs | None => [] end.

Definition shape_addr (n : Z) (w0 : list byte) : Z :=
  if n =? 0 then SHAPE_LIT else shape_find shape_rows w0.

Definition refusal_text (c : Z) : list byte := pf_bytes ([114; 101; 115; 112; 32] ++ pf_dec c).

Definition reply_ok (n : Z) (w0 xr : list byte) : Prop :=
  (reply_code xr < 0 -> declared (reply_code xr) = true /\ xr = refusal_text (reply_code xr)) /\
  (0 <= reply_code xr ->
     reply_matches (img_str (shape_addr n w0)) xr = true \/ reply_matches (img_str SHAPE_LIT) xr = true).

Definition check_reply_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (ans rep ww p0 : word) (xr slack xa w0 sl0 : list byte) (n : Z) (can : word),
    mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_REPLY_K <= bv_unsigned sp -> IMG_END <= lo ->
    bv_unsigned sp < 2^63 ->
    rw_cells rsegs m GOT_GUARD [C8 (Z_to_bv 64 GUARD)] -> rw_cells rsegs m GUARD [C8 can] ->
    bytes_at rsegs m GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
    bytes_at rsegs m (G_REC + REC_ANSWER) (le8 ans) ->
    bytes_at rsegs m (G_REC + REC_NREPLIES) (le4 (Z_to_bv 64 1)) ->
    bytes_at rsegs m (G_REC + REC_REPLY) (le8 rep) ->
    bytes_at rsegs m (G_REC + REC_REPLY_SIZE) (le8 (Z_to_bv 64 (Z.of_nat (length xr) + 1))) ->
    bytes_at rsegs m G_SHAPES g_shapes_bytes ->
    bv_unsigned rep <> 0 ->
    bytes_at rsegs m (bv_unsigned rep) (xr ++ NUL :: slack) -> ~ In NUL xr ->
    (- (bv_unsigned rep + Z.of_nat (length xr) + 1)) mod 8 <= Z.of_nat (length slack) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned rep) (Z.of_nat (length xr) + 1 + Z.of_nat (length slack)) ->
    (bv_unsigned ans <> 0 ->
       cstr_at m (bv_unsigned ans) xa /\ outside_stack lo (bv_unsigned sp) (bv_unsigned ans) (Z.of_nat (length xa) + 1)) ->
    0 <= n < 2^31 ->
    bytes_at rsegs m (bv_unsigned a0 + WORDS_N) (le4 (Z_to_bv 64 n)) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + WORDS_N) 4 ->
    bytes_at rsegs m (bv_unsigned a0 + WORDS_W) (le8 ww) ->
    outside_stack lo (bv_unsigned sp) (bv_unsigned a0 + WORDS_W) 8 ->
    (n <> 0 ->
       bytes_at rsegs m (bv_unsigned ww) (le8 p0) /\ outside_stack lo (bv_unsigned sp) (bv_unsigned ww) 8 /\
       bytes_at rsegs m (bv_unsigned p0) (w0 ++ NUL :: sl0) /\ ~ In NUL w0 /\
       (- (bv_unsigned p0 + Z.of_nat (length w0) + 1)) mod 8 <= Z.of_nat (length sl0) /\
       outside_stack lo (bv_unsigned sp) (bv_unsigned p0) (Z.of_nat (length w0) + 1 + Z.of_nat (length sl0))) ->
    answer_ok ans xr xa n w0 ->
    reply_ok n w0 xr ->
    evt rsegs (fp_void_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_REPLY) fc None m (seg_rom rsegs)).
