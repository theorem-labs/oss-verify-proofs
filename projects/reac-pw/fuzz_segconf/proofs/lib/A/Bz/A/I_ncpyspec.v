(* The statement musl's strncpy of reac-pw/fuzz_segconf's ASan image A meets (0x9ad50, 40 B, which calls __stpncpy
   0x9ad78, 272 B, which pads through the memset wrapper: trampoline 0x558d8, wrapper 0x55fbc), in the Bz kit's form,
   for the strncpy wrapper walk I_strncpyw.v, which takes it as a Section hypothesis, and for I_stpncpyA.v, which
   proves it. The form follows proofs/pupnp/FuzzHttp/lib/A0/ICP/M_stpncpy.v strncpy_spec (origin/ossv/recipes),
   generalized on the source: either the string's NUL is among the bytes the loops reach (the string, its NUL and
   the slack to the end of the NUL's word, as pupnp states it), or the first n bytes hold no NUL and only those n
   bytes are stated. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import R_small R_m2s I_consts I_qck I_memsetw.
Import ListNotations.
Open Scope Z_scope.

Definition strncpyA_entry : Z := 0x9ad50.

(* strncpy's 16-byte frame, __stpncpy's 16-byte frame, then the memset wrapper (I_imemset.v IMEMSET_DEPTH) *)
Notation ISTRNCPYA_DEPTH := 2256%Z (only parsing).

(* The bytes strncpy(d, s, n) leaves at d: the first min(|str|, n) bytes of str, then NUL bytes up to n. *)
Definition stpn_k (str : list byte) (n : nat) : nat := Nat.min (length str) n.
Definition stpn_result (str : list byte) (n : nat) : list byte :=
  firstn (stpn_k str n) str ++ repeat (Z_to_bv 8 0) (n - stpn_k str n).

(* What the copy reads at s: [src]. Either the string str, its NUL and enough slack to fill the NUL's word, or,
   when str is at least n bytes long, its first n bytes alone. *)
Definition ncpy_src (s : Z) (n : nat) (str src : list byte) : Prop :=
  ~ In (Z_to_bv 8 0) str /\
  ((exists slack, src = str ++ Z_to_bv 8 0 :: slack /\
                  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)) \/
   ((n <= length str)%nat /\ src = firstn n str)).

(* The range check of every tail of the destination (the padding memset checks [d + k, d + n)). *)
Definition chk_tails (m : mem) (d n : Z) : Prop := forall i, 0 <= i <= n -> chk_ok m (d + i) (n - i).

(* The runtime cells the memset wrapper reads after the copy (I_memsetw.v icells_ms, R_m2s.v m2s_cells): the
   destination lies apart from each (no bytes are copied when n = 0). *)
Definition NCPY_CELLS : list (Z * Z) :=
  [ (0xa2a50, 32); (0xa35b8, 8); (0xa48e8, 8); (0xabff8, 8); (0xaccd9, 1); (0xacce0, 24) ].
Definition ncpy_cells_apart (d n : Z) : Prop :=
  n = 0 \/ Forall (fun c : Z * Z => d + n <= fst c \/ fst c + snd c <= d) NCPY_CELLS.

Definition strncpyA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d n : Z) (str : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + n); (bv_unsigned sp - ISTRNCPYA_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' d [CB (Z.to_nat n) (stpn_result str (Z.to_nat n))].

Definition strncpyA_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s n : Z) (str src junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCPYA_DEPTH -> kHighShadowEnd < lo ->
  bv_unsigned sp <= 2^47 ->
  0 <= s -> 0 <= d -> 0 <= n < 2^32 -> s + Z.of_nat (length src) <= 2^47 -> d + n <= 2^47 ->
  bytes_at asegs m s src -> ncpy_src s (Z.to_nat n) str src ->
  rw_cells asegs m d [CB (Z.to_nat n) junk] ->
  (d + n <= s \/ s + Z.of_nat (length src) <= d) ->
  (n = 0 \/ s + Z.of_nat (length src) <= lo \/ bv_unsigned sp <= s) ->
  (n = 0 \/ d + n <= lo \/ bv_unsigned sp <= d) ->
  chk_tails m d n -> ncpy_cells_apart d n ->
  m2s_cells m -> icells_ms m -> mem_inv asegs m ->
  evt asegs (strncpyA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d n str lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strncpyA_entry) fc None m (seg_rom asegs)).

Lemma stpn_result_length : forall str n, length (stpn_result str n) = n.
Proof. intros. unfold stpn_result, stpn_k. rewrite app_length, firstn_length, repeat_length. lia. Qed.
