(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the states segment S_E01 of
   the walk of LLVMFuzzerTestOneInput (ENTRY 0x80714 -> C1 0x809e0, lib/A/RtPgSeg.v S_E01) is split at, and the
   statement of each of its four parts. Statement text only: no function is proved here (kind: segment lemma, its
   parts).

   THE SPLIT. Four runs, each from one state to the next, in RtPgSeg's continuation form ("from the next state the
   rest realizes POST -> from this state it does"):
   - ENT, ENTRY 0x80714 -> FR 0x80788: the prologue (`addi sp,sp,-0x1e0`, `sd zero,0(sp)`, the 13 saves at
     [S - 0x68, S), s0 = S, sp = s1 = R = (S - 0x1e0) & -32, s5 = n, s9 = p), the two GOT loads (0x9be70 -> the
     shadow offset into s2, 0x9bec8 -> the option byte, 1, so `beqz a2` 0x8077c falls through), `addi a0,zero,0x1c0`
     and the call __asan_stack_malloc_3(448) (`jal` 0x80784 -> 0x3d2c8, ra = 0x80788), which returns the class-3
     frame F = frame_addr (entry layout) 3 pos and its flag pointer word at F + 0x1f8;
   - PRO, FR 0x80788 -> HD 0x808e4: s8 = s10 = F, `bnez s8` 0x80798 taken (F >= 4096), R + 0x150 := F, the frame
     header F[0], F[8], F[16] (0x807e0 .. 0x807e8), s4 = (F >> 3) + K, the 56 frame-shadow stores 0x807f4 ..
     0x808d8 (RtPgImgA.rate_A_shA), and the size test `srli a2,s5,0x1a` / `beqz a2` 0x808dc, which falls through
     because n < 2^26;
   - HDR, HD 0x808e4 -> CALL 0x52bb4: the seven header reads (fuzz_rate.c:236-239, fuzz.h:37-49) in their eight
     input-length arms (n = 0 .. 6, n >= 7; the inline block 0x808e4 .. 0x809dc and the out-of-line block 0x82b94 ..
     0x82c40), each read behind its instrumented 1-byte check (the inline ones 0x808f0 / 0x80948 / 0x80978 of the
     `beqz t,+8; j L` shape, the out-of-line ones 0x82b9c / 0x82bc8 / 0x82bf8 / 0x82c24 of the `bnez` shape), the
     spills of the seven values, s3 = 0x5000, s5 = a0 = 19744, and the `jal` of malloc 0x809dc (ra = 0x809e0);
   - CALL, CALL 0x52bb4 -> C1 0x809e0: the call malloc(19744) (lib/Reusable YCbq aj_malloc_at04) and C1
     (RtPgSeg rh_cut_C1).

   WHAT EACH STATE CARRIES. Every state carries e01_base: the harness journal from the entry (RtPgSeg rh_j, FP = [],
   own = [(3, pos)], no event yet), the frame as the only frame, the entry's blocks, the 13 saves and the flag
   pointer word (RtPgSeg rh_kept, at the geometry of e01_env), and the input bytes at p. FR adds the registers the
   prologue set; HD adds s4, s8, s10 and the frame's shadow bytes; CALL is the call state (role's form): every value
   of C1's list but its first (a0 = pp, which only the call gives). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg.
From OSSVerify.reac_pw.fuzz_rate.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition E01_SM3 : Z := 0x3d2c8.        (* __asan_stack_malloc_3, called at 0x80784 *)
Definition E01_FR : Z := 0x80788.         (* its return: `mv s8,a0` *)
Definition E01_HD : Z := 0x808e4.         (* `beqz s5` (fuzz.h:39), the header's first input-length test *)
Definition E01_MALLOC : Z := 0x52bb4.     (* the malloc trampoline, called at 0x809dc *)
Definition E01_MALLOC_RA : Z := 0x809e0.  (* = C1 *)
(* the frame request a0 = 0x1c0 (0x80780) and the first block's size a0 = s5 = 19744 (0x809d0 .. 0x809d8) *)
Definition E01_FRAME_REQ : Z := 0x1c0.
Lemma E01_pp_size : Layout.PP_SIZE = 0x5000 - 0x2e0.
Proof. reflexivity. Qed.
Lemma E01_ra_c1 : E01_MALLOC_RA = RS_C1.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ======================================== the geometry ========================================
   S the entry sp, R = 32 * floor((S - 0x1e0) / 32) the base of the real frame (s1 and sp from 0x80758), F the
   class-3 frame at pos of the entry layout (RtPgSeg rh_geo). e01_env carries only these three; RtPgSeg's rh_kept
   reads only q_S and q_F of its environment. *)
Definition e01_S (hx : rh_hcx rsegs) : Z := spZ (h_regs rsegs hx).
Definition e01_R (hx : rh_hcx rsegs) : Z := 32 * ((e01_S hx - RS_RSZ) / 32).
Definition e01_F (hx : rh_hcx rsegs) (pos : Z) : Z := frame_addr (h_ly rsegs hx) RS_CID pos.
Definition e01_env (hx : rh_hcx rsegs) (pos : Z) : rt_renv :=
RtEnv (e01_S hx) (e01_R hx) (e01_F hx pos) 0 0 0 0 0 0 0 0 0 0 0 0 0.

Lemma e01_geo_env : forall hx pos, rh_geo rsegs hx pos (e01_env hx pos).
Proof. intros hx pos. unfold rh_geo, e01_env, e01_R, e01_S, e01_F. cbn. repeat split. Qed.

(* rh_kept reads its environment only through q_S and q_F, and no register *)
Lemma e01_kept_env : forall hx pos e e' (W : world rsegs) mem regs regs',
q_S e' = q_S e -> q_F e' = q_F e ->
rh_kept rsegs hx pos e W mem regs -> rh_kept rsegs hx pos e' W mem regs'.
Proof.
intros hx pos e e' W mem regs regs' ES EF Hk. unfold rh_kept, rh_cells in *.
rewrite Forall_forall in *. intros f Hf. pose proof (Hk f Hf) as Hf'.
apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
- unfold rh_saves_L in Hf. apply in_map_iff in Hf as (j & <- & _).
  cbn [fst snd rt_at rt_xv] in *. rewrite ES. exact Hf'.
- cbn [fst snd rt_at rt_xv] in *. rewrite EF. exact Hf'.
Qed.

(* ======================================== the states ======================================== *)
(* What every state of the segment carries (see the header). *)
Definition e01_base (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(mem : word -> option byte) (md : Model) : Prop :=
rh_j rsegs B LLVMF_STK hx [(RS_CID, pos)] lyc Sc W mem md 0 /\
frames Sc = [(RS_CID, pos)] /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rh_kept rsegs hx pos (e01_env hx pos) W mem (h_regs rsegs hx) /\
garr8 rsegs (mrestrict (w_H W) mem) (h_p rsegs hx) (map (fun b : byte => bv_unsigned b) (h_pl rsegs hx)).

(* FR = 0x80788, __asan_stack_malloc_3 returned: sp = s1 = R, gp, tp, s0 = S, s2 = the shadow offset, s5 = n,
   s9 = p, a0 = F. *)
Definition e01_fr (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
e01_base hx pos lyc Sc W mem md /\
getr regs 2 = w64 (e01_R hx) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e01_S hx) /\ getr regs 9 = w64 (e01_R hx) /\ getr regs 18 = w64 SHADOW_OFF /\
getr regs 21 = w64 (h_n rsegs hx) /\ getr regs 25 = w64 (h_p rsegs hx) /\
getr regs 10 = w64 (e01_F hx pos).

(* HD = 0x808e4, the frame's header and shadow written: FR's registers but a0, and s4 = (F >> 3) + K,
   s8 = s10 = F; the frame's 56 shadow bytes rate_A_shA. *)
Definition e01_hd (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
e01_base hx pos lyc Sc W mem md /\
getr regs 2 = w64 (e01_R hx) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e01_S hx) /\ getr regs 9 = w64 (e01_R hx) /\ getr regs 18 = w64 SHADOW_OFF /\
getr regs 20 = w64 (shadow_addr (e01_F hx pos)) /\ getr regs 21 = w64 (h_n rsegs hx) /\
getr regs 24 = w64 (e01_F hx pos) /\ getr regs 25 = w64 (h_p rsegs hx) /\ getr regs 26 = w64 (e01_F hx pos) /\
rt_fsh rsegs (w_H W) mem (e01_F hx pos) rate_A_shA.

(* The input after the 7-byte header at a state: rest at the cursor q_src (rate_build_contract's garr8 form), its
   length, the cursor's bounds, and where it lies: nothing is left, or it is inside one of the entry's blocks (the
   input block). *)
Definition e01_in (hx : rh_hcx rsegs) (W : world rsegs) (mem : word -> option byte) (e : rt_renv) (rest : list byte)
: Prop :=
q_left e = Z.of_nat (length rest) /\
garr8 rsegs (mrestrict (w_H W) mem) (q_src e) (map (fun x : byte => bv_unsigned x) rest) /\
0 < q_src e /\ q_src e + q_left e <= 2 ^ 63 /\ amem_range (q_src e) (q_left e) /\
(q_left e = 0 \/
 exists p n, In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\ p <= q_src e /\
   q_src e + q_left e <= p + req_size n).

(* CALL = 0x52bb4, at the `jal` of malloc(19744) 0x809dc (ra = 0x809e0): the harness journal, the frame, the
   entry's blocks, the geometry, ra / sp / gp / tp, a0 = 19744, every value of C1's list hi_L1 but its first
   (a0 = pp, which only the call gives), the frame's shadow, the header values' bounds and their tie to the input
   (rh_hdr: q_fl .. q_b6 the header bytes, rest = skipn 7 of the input, src / left / len), the carried cells and the
   input after the header. q_pp, q_pod, q_buf are free here. *)
Definition e01_call_facts (hx : rh_hcx rsegs) (pos : Z) (e : rt_renv) (rest : list byte)
(lyc : alayout) (Sc : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
rh_j rsegs B LLVMF_STK hx [(RS_CID, pos)] lyc Sc W mem md 0 /\
frames Sc = [(RS_CID, pos)] /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rh_geo rsegs hx pos e /\
getr regs 1 = w64 E01_MALLOC_RA /\ getr regs 2 = w64 (q_R e) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 Layout.PP_SIZE /\
rt_cut rsegs (w_H W) mem regs e (tl (hi_L1 rate_himg_A)) /\
rt_fsh rsegs (w_H W) mem (q_F e) rate_A_shA /\
rt_hdr_ok e /\ rh_hdr rsegs hx e rest /\
rh_kept rsegs hx pos e W mem regs /\
e01_in hx W mem e rest.

(* ======================================== the continuations ======================================== *)
Definition e01_from_fr (hx : rh_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos lyc Sc W regs mem md, e01_fr hx pos lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01_FR regs mem md) POST.
Definition e01_from_hd (hx : rh_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos lyc Sc W regs mem md, e01_hd hx pos lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01_HD regs mem md) POST.
Definition e01_from_call (hx : rh_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos e rest lyc Sc W regs mem md, e01_call_facts hx pos e rest lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01_MALLOC regs mem md) POST.

(* ======================================== the four parts ======================================== *)
Definition e01_ent_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01_from_fr hx POST ->
SRr rsegs (h_W rsegs hx) (cfg_at rsegs RS_ENTRY (h_regs rsegs hx) (h_mem rsegs hx) (h_md rsegs hx)) POST.
Definition e01_pro_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01_from_hd hx POST -> e01_from_fr hx POST.
Definition e01_hdr_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01_from_call hx POST -> e01_from_hd hx POST.
Definition e01_call_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> rh_from_C1 rsegs B LLVMF_STK hx POST ->
e01_from_call hx POST.

(* The four parts compose into S_E01. *)
Lemma e01_chain : e01_ent_stmt -> e01_pro_stmt -> e01_hdr_stmt -> e01_call_stmt ->
S_E01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros HE HP HH HC hx POST Hb HK.
exact (HE hx POST Hb (HP hx POST Hb (HH hx POST Hb (HC hx POST Hb HK)))).
Qed.

(* The allocation trace of the malloc(pp) call site (return address 0x809e0): the trace the allocator records is
   its own return pc, then 0x809e0, then the harness's return address when the entry frame is chained. *)
Definition e01_trace_stmt : Prop :=
forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
raZ regsT = E01_MALLOC_RA ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
End b.
