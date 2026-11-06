(* Modified by Theorem Labs, 2026-10: asan-ubsan twin of lib/U/Prog/strtod_c.v for the #102 fuzz_preset images (facts 8f3e7e1a07f1; asan-ubsan pin sha256 d663f82d7f488d30), through lib/CJ/RL/I/IImgB.v and InstB.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Open Scope Z_scope.

(* #102: each value is read BY SYMBOL from the asan-ubsan image's unstripped twin (sha256 c90d4fa54d43160b):
   STRTOD = strtod; STRTOD_GUARD = __stack_chk_guard; STRTOD_GOT_GUARD = the one .got cell holding it;
   STRTOD_TP = builtin_tls + 0xc8 (G_Scan_iface RATP, key 0x341f8); STRTOD_ERRNO = STRTOD_TP - 164 (RERRNO);
   STRTOD_GLOBALS_TOP = page ceiling of the last PT_LOAD end (0x600010 at #102, so 0x601000, = YImgTop IMG_TOP_B);
   STRTOD_IMG_LO = lowest PT_LOAD; STRTOD_K = RSTRTOD_DEPTH.
   The strtod_c_* lemmas below check them against the image by vm_compute. *)
Definition STRTOD : Z := 0x9b740.
Definition STRTOD_K : Z := 8928.
Definition STRTOD_TP : Z := 0x5de730.
Definition STRTOD_ERRNO : Z := 0x5de68c.
Definition STRTOD_GOT_GUARD : Z := 0xa34d8.
Definition STRTOD_GUARD : Z := 0x5fe770.
Definition STRTOD_GLOBALS_TOP : Z := 0x601000.
Definition STRTOD_IMG_LO : Z := 0x10000.

Definition strtod_c_rom_b (a : Z) (bs : list Z) : bool :=
  forallb (fun k => match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat k)) with
                    | Some b => Z.eqb (bv_unsigned b) (nth k bs 0) | None => false end) (seq 0 (length bs)).

(* strtod's first 16 code bytes (addi sp,sp,-272; sd ra,264(sp); sd s0,256(sp); sd s1,248(sp)) are at STRTOD *)
Lemma strtod_c_code : strtod_c_rom_b STRTOD [19; 1; 1; 239; 35; 52; 17; 16; 35; 48; 129; 16; 35; 60; 145; 14] = true.
Proof. vm_compute. reflexivity. Qed.

(* the .got cell STRTOD_GOT_GUARD holds STRTOD_GUARD (little endian) *)
Lemma strtod_c_got :
  strtod_c_rom_b STRTOD_GOT_GUARD (map (fun k => Z.land (Z.shiftr STRTOD_GUARD (8 * Z.of_nat k)) 255) (seq 0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

(* the errno cell and the thread-pointer byte lie in the image (builtin_tls, zero at load) *)
Lemma strtod_c_tls : STRTOD_ERRNO = STRTOD_TP - 164 /\ strtod_c_rom_b STRTOD_ERRNO [0; 0; 0; 0] = true /\
  strtod_c_rom_b (STRTOD_TP - 1) [0] = true.
Proof. split; [reflexivity|]. split; vm_compute; reflexivity. Qed.

(* every segment lies in [STRTOD_IMG_LO, STRTOD_GLOBALS_TOP); one starts at STRTOD_IMG_LO; one ends in the last page *)
Lemma strtod_c_segs :
  forallb (fun sg => (STRTOD_IMG_LO <=? Z.of_N (seg_base sg)) &&
                     (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? STRTOD_GLOBALS_TOP)) rsegs = true /\
  existsb (fun sg => Z.of_N (seg_base sg) =? STRTOD_IMG_LO) rsegs = true /\
  existsb (fun sg => STRTOD_GLOBALS_TOP - 4096 <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) rsegs = true /\
  STRTOD_GLOBALS_TOP mod 4096 = 0.
Proof. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity. Qed.

Definition strtod_model (txt : list Z) : option (Z * Z) := FloatScan.scan_strtod (txt ++ [0]).

Definition strtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s e : Z) (txt : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte) (ev' : word) (c bits : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ strtod_model txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt)
    /\ rw_cells rsegs m' e [C8 (Z_to_bv 64 (s + c))]
    /\ reg_get F' 10 = Z_to_bv 64 bits
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ frm0 fc'
    /\ rw_cells rsegs m' STRTOD_ERRNO [C4 ev']
    /\ munch [(bv_unsigned sp - STRTOD_K, bv_unsigned sp); (e, e + 8); (STRTOD_ERRNO, STRTOD_ERRNO + 4)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - STRTOD_K) (bv_unsigned sp).

Definition strtod_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (s e : Z) (txt : list Z) (ejunk canary ev : word),
    a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 e -> tp = Z_to_bv 64 STRTOD_TP ->
    bytes_at rsegs m s (map (Z_to_bv 8) (txt ++ [0])) ->
    Forall (fun c => FmtFp_facts3.is_numch c = true) txt -> Z.of_nat (length txt) < 2^30 ->
    rw_cells rsegs m e [C8 ejunk] ->
    stk rsegs m (bv_unsigned sp - STRTOD_K) (bv_unsigned sp) ->
    STRTOD_GLOBALS_TOP <= bv_unsigned sp - STRTOD_K -> bv_unsigned sp < 2^62 ->
    4096 <= s -> s + Z.of_nat (length txt) + 1 <= 2^62 ->
    ((s + Z.of_nat (length txt) + 1 <= STRTOD_IMG_LO \/ STRTOD_GLOBALS_TOP <= s)
       /\ s + Z.of_nat (length txt) + 1 <= bv_unsigned sp - STRTOD_K
     \/ bv_unsigned sp <= s) ->
    (STRTOD_GLOBALS_TOP <= e /\ e + 8 <= bv_unsigned sp - STRTOD_K \/ bv_unsigned sp <= e) -> e + 8 <= 2^62 ->
    (e + 8 <= s \/ s + Z.of_nat (length txt) + 1 <= e) ->
    rw_cells rsegs m STRTOD_GOT_GUARD [C8 (Z_to_bv 64 STRTOD_GUARD)] -> rw_cells rsegs m STRTOD_GUARD [C8 canary] ->
    rw_cells rsegs m STRTOD_ERRNO [C4 ev] ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
    evt rsegs (strtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s e txt m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRTOD) fc None m (seg_rom rsegs)).
