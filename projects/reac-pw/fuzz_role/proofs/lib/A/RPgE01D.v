(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the definitions the walk
   of segment S_E01 of LLVMFuzzerTestOneInput (ENTRY 0x7ff88 -> K80194, lib/A/RPgHarn.v rh_S_E01_stmt) is split
   over. Statement text only: no function is proved here (kind: segment lemma, its parts).

   THE SPLIT. The walk runs the engine (lib/Reusable YCbq aj_run_to over the code table E01_TBL) from the entry to
   the `jal` of malloc(pp) at 0x80190, with the class-3 frame call __asan_stack_malloc_3(416) at 0x7fff8 in the
   middle (YCbq aj_stack_malloc_at). It stops at the malloc entry 0x52428 with the facts e01_call_facts; the last
   part, e01_call_stmt, makes the call (YCbq aj_malloc_at04) and builds RPgHarn's K80194 cut rh_at_C1 from them.

   THE CALL STATE (e01_call_facts), at the `jal` 0x80190 -> 0x52428 (ra = 0x80194):
   - the harness journal from the entry (RPgHarn rh_j: FP = [], own = [(3, pos)], no event yet), the blocks as at
     the entry (__asan_stack_malloc_3 keeps them);
   - the geometry (RPgHarn rh_geo: S the entry sp, R = 32 * ((S - 0x1a0) / 32), F = frame_addr of the entry layout
     at class 3, pos);
   - the registers: sp = R, gp / tp, ra = 0x80194, a0 = 19744 (0x80184-0x8018c: `lui s4,5`, `addiw s2,s4,-0x2e0`,
     `mv a0,s2`), and every other value of K80194's list hi_L1 (RPgImgA: s0 = S, s1 = R, s2 = 19744,
     s3 = (F >> 3) + K, s4 = 0x5000, s5 = the bytes left, s6 = s9 = F, s7 = K; R+0x30 = the flags byte,
     R+0xc8 = the cursor): all of hi_L1 but its first entry (a0 = pp, which only the call gives);
   - the frame's 52 shadow bytes after the prologue (RPgImgA role_A_shA, stored at 0x8006c-0x8013c);
   - the carried cells (RPgHarn rh_kept: the 13 saves at S - 8 - 8 j, the flag pointer word at F + 0x1f8);
   - the input after the flags byte (e01_in): rest at the cursor, with the cursor's bounds, inside one of the
     entry's blocks unless nothing is left. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgHarn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== the code ========================================
   The segment's instructions, read from image A's loaded segments (lib/A/Img0.v rsegs): the 131 words
   0x7ff88 .. 0x80190 (the prologue, the frame call, the frame's header and shadow, the size test, the flags byte
   with its shadow check, the malloc(pp) request), and the check's slow block 0x82610 .. 0x82618 (`andi a1,a2,7`;
   `bge a1,a0` to the report; `j 0x80164`). The report call at 0x8261c and the real-stack arm's probe loop
   0x8001c .. 0x80024 are in no run: the walk shows each branch to them is not taken. *)
Definition E01_A : Z := 0x7ff88.
Definition E01_N : nat := 131.
Definition E01_SLOW : Z := 0x82610.
Definition E01_TBL : ctable := build_table rsegs E01_SLOW 3 (build_table rsegs E01_A E01_N TEmpty).
Lemma E01_TBL_ok : table_ok rsegs E01_TBL.
Proof. apply build_table_ok; [unfold E01_SLOW; lia|]. apply build_table_ok0. unfold E01_A. lia. Qed.
(* the pcs the walk stops at *)
Definition E01_SM3 : Z := 0x3cbfc.      (* __asan_stack_malloc_3, called at 0x7fff8 with ra = 0x7fffc *)
Definition E01_SM3_RA : Z := 0x7fffc.
Definition E01_MALLOC : Z := 0x52428.   (* the malloc trampoline, called at 0x80190 with ra = 0x80194 *)
Definition E01_MALLOC_RA : Z := 0x80194.
(* the frame request a0 = 0x1a0 (0x7fff4) and the first block's size a0 = 19744 (0x80184 .. 0x8018c) *)
Definition E01_FRAME_REQ : Z := 0x1a0.
Lemma E01_pp_size : Layout.PP_SIZE = 0x5000 - 0x2e0.
Proof. reflexivity. Qed.
Lemma E01_ra_c1 : E01_MALLOC_RA = RH_C1.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* The input after the flags byte at a state: rest at the cursor e_src (role_build_contract's garr8 form), its
   length and pod length, the cursor's bounds, and where it lies: nothing is left, or it is inside one of the
   entry's blocks (the input block). *)
Definition e01_in (hx : rh_hcx rsegs) (W : world rsegs) (mem : word -> option byte) (e : rl_env) (rest : list byte)
: Prop :=
e_left e = Z.of_nat (length rest) /\ e_len e = rl_len rest /\
garr8 rsegs (mrestrict (w_H W) mem) (e_src e) (map (fun x : byte => bv_unsigned x) rest) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(e_left e = 0 \/
 exists p n, In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\ p <= e_src e /\ e_src e + e_left e <= p + req_size n).

(* The state at the `jal` of malloc(pp), pc 0x52428 (see the header). e_pp is free here: the call gives pp. *)
Definition e01_call_facts (hx : rh_hcx rsegs) (pos : Z) (e : rl_env) (rest : list byte)
(lyc : alayout) (Sc : astate) (W : world rsegs) (regsT : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
: Prop :=
rh_j rsegs B LLVMF_STK hx [(RH_CID, pos)] lyc Sc W memc mdc 0 /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rh_geo rsegs hx pos e /\
getr regsT 1 = w64 E01_MALLOC_RA /\ getr regsT 2 = w64 (e_R e) /\
getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\
getr regsT 10 = w64 Layout.PP_SIZE /\
rl_cut rsegs (w_H W) memc regsT e (tl (hi_L1 role_himg_A)) /\
rl_fsh rsegs (w_H W) memc (e_F e) role_A_shA /\
0 <= e_fl e < 256 /\
rh_kept rsegs hx pos e W memc regsT /\
e01_in hx W memc e rest.

(* The last part: from the call state, the call and K80194. *)
Definition e01_call_stmt : Prop :=
forall (hx : rh_hcx rsegs) pos e rest lyc Sc W regsT memc mdc,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01_call_facts hx pos e rest lyc Sc W regsT memc mdc ->
SRr rsegs W (cfg_at rsegs E01_MALLOC regsT memc mdc) (rh_at_C1 rsegs B LLVMF_STK hx).

(* The allocation trace of the malloc(pp) call site (return address 0x80194): the trace the allocator records
   is its own return pc, then 0x80194, then the harness's return address when the entry frame is chained
   (scene's P_LLVMFuzzerTestOneInput_ctx.rt_trace_in_stmt, at this one site). *)
Definition e01_trace_stmt : Prop :=
forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
raZ regsT = E01_MALLOC_RA ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
End b.
