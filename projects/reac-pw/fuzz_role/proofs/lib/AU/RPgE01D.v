(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01D.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's pcs, registers and frame class; the harness records of lib/AU/RtPgSegB.v
   (rhb_ names) and the frame shadow pattern rsb_P0 of 88 bytes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgE01DB.v at 48db065d2b9c; for reac-pw/fuzz_role
   image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the harness records of lib/AU/RPgHarn.v (rh_
   names, RPgBase's rl_env), role B's pcs (frame entry 0x3cc74, FR 0x80094, HD 0x80270, malloc 0x524c0, C1 0x802c4),
   registers (n in s2, p in s5, the shadow offset in s11, F in s7 and s10), the real frame 0x200, the frame shadow
   pattern hi_shA role_himg_B, and role's one-byte header (rh_hdr, the flags byte's bound) in the call state. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the states segment S_E01 of
   the walk of LLVMFuzzerTestOneInput (ENTRY 0x80020 -> C1 0x802c4, lib/AU/RPgHarn.v S_E01) is split at, and the
   statement of each of its four parts. Statement text only: no function is proved here (kind: segment lemma, its
   parts).

   THE SPLIT. Four runs, each from one state to the next, in RPgHarn's continuation form ("from the next state the
   rest realizes POST -> from this state it does"):
   - ENT, ENTRY 0x80020 -> FR 0x80094: the prologue (`addi sp,sp,-0x200`, `sd zero,0(sp)`, the 13 saves at
     [S - 0x68, S), s0 = S, sp = s1 = R = (S - 0x200) & -32, s2 = n), the two GOT loads (0x9ab28 -> the option
     byte, 1, so `beqz a2` 0x80088 falls through; 0x9aad0 -> the shadow offset into s11), s5 = p, `li a0,704` and
     the call frame_alloc_4(704) (`jal` 0x80090 -> 0x3cc74, ra = 0x80094), which returns the class-4 frame
     F = frame_addr (entry layout) 4 pos and its flag pointer word at F + 0x3f8;
   - PRO, FR 0x80094 -> HD 0x80270: s7 = s10 = F, `bnez s7` 0x800a4 taken (F >= 4096), R + 0x170 := F, the frame
     header F[0], F[8], F[16] (0x800f0 .. 0x800f8), s3 = (F >> 3) + K, the 88 frame-shadow stores 0x80104 ..
     0x80264 (RPgImgA hi_shA role_himg_B), and the size test `srli a3,s2,0x1a` 0x80114 / `beqz a3` 0x80268, which is
     taken because n < 2^26;
   - HDR, HD 0x80270 -> CALL 0x524c0: the one header read (fuzz_role.c flags = fuzz_u8, fuzz.h:37-43) in its two
     input-length arms (n = 0: R+0x40 := 0, s6 = 0, s4 = p; n >= 1: the UBSan pointer-overflow test `bltu` 0x8027c,
     the instrumented 1-byte check 0x80284 .. 0x80294 with its slow block 0x8264c .. 0x82654, `lbu` 0x80298,
     R+0x40 := fl, s6 = n - 1, s4 = p + 1), s5 = 0x5000, s2 = a0 = 19744, and the `jal` of malloc 0x802c0
     (ra = 0x802c4);
   - CALL, CALL 0x524c0 -> C1 0x802c4: the call malloc(19744) (lib/Reusable YCbq aj_malloc_at04) and C1
     (RPgHarn rh_cut_C1).

   WHAT EACH STATE CARRIES. Every state carries e01b_base: the harness journal from the entry (RPgHarn rh_j, FP =
   [], own = [(4, pos)], no event yet), the frame as the only frame, the entry's blocks, the 13 saves and the flag
   pointer word (RPgHarn rh_kept, at the geometry of e01b_env), and the input bytes at p. FR adds the registers
   the prologue set; HD adds s3, s7, s10 and the frame's shadow bytes; CALL is the call state: every value of C1's
   list but its first (a0 = pp, which only the call gives). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgHarn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition E01B_SM4 : Z := 0x3cc74.        (* __asan_stack_malloc_4, called at 0x80090 *)
Definition E01B_FR : Z := 0x80094.         (* its return: `mv s7,a0` *)
Definition E01B_HD : Z := 0x80270.         (* `beqz s2` (fuzz.h:39), the header's input-length test *)
Definition E01B_MALLOC : Z := 0x524c0.     (* the malloc trampoline, called at 0x802c0 *)
Definition E01B_MALLOC_RA : Z := 0x802c4.  (* = C1 *)
(* the frame request a0 = 0x2c0 (0x8008c) and the first block's size a0 = s2 = 19744 (0x802b4 .. 0x802bc) *)
Definition E01B_FRAME_REQ : Z := 0x2c0.
Lemma E01B_pp_size : Layout.PP_SIZE = 0x5000 - 0x2e0.
Proof. reflexivity. Qed.
Lemma E01B_ra_c1 : E01B_MALLOC_RA = RH_C1.
Proof. reflexivity. Qed.
Lemma E01B_cid : RH_CID = hi_cid role_himg_B.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ======================================== the geometry ========================================
   S the entry sp, R = 32 * floor((S - 0x200) / 32) the base of the real frame (s1 and sp from 0x80064), F the
   class-4 frame at pos of the entry layout (RPgHarn rh_geo). e01b_env carries only these three; RPgHarn's
   rh_kept reads only e_S and e_F of its environment. *)
Definition e01b_S (hx : rh_hcx rsegs) : Z := spZ (h_regs rsegs hx).
Definition e01b_R (hx : rh_hcx rsegs) : Z := 32 * ((e01b_S hx - RH_RSZ) / 32).
Definition e01b_F (hx : rh_hcx rsegs) (pos : Z) : Z := frame_addr (h_ly rsegs hx) RH_CID pos.
Definition e01b_env (hx : rh_hcx rsegs) (pos : Z) : rl_env :=
RLEnv (e01b_S hx) (e01b_R hx) (e01b_F hx pos) 0 0 0 0 0 0.

Lemma e01b_geo_env : forall hx pos, rh_geo rsegs hx pos (e01b_env hx pos).
Proof. intros hx pos. unfold rh_geo, e01b_env, e01b_R, e01b_S, e01b_F. cbn. repeat split. Qed.

(* rh_kept reads its environment only through e_S and e_F, and no register *)
Lemma e01b_kept_env : forall hx pos e e' (W : world rsegs) mem regs regs',
e_S e' = e_S e -> e_F e' = e_F e ->
rh_kept rsegs hx pos e W mem regs -> rh_kept rsegs hx pos e' W mem regs'.
Proof.
intros hx pos e e' W mem regs regs' ES EF Hk. unfold rh_kept, rh_cells in *.
rewrite Forall_forall in *. intros f Hf. pose proof (Hk f Hf) as Hf'.
apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
- unfold rh_saves_L in Hf. apply in_map_iff in Hf as (j & <- & _).
  cbn [fst snd rl_at rl_xv] in *. rewrite ES. exact Hf'.
- cbn [fst snd rl_at rl_xv] in *. rewrite EF. exact Hf'.
Qed.

(* ======================================== the states ======================================== *)
(* What every state of the segment carries (see the header). *)
Definition e01b_base (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(mem : word -> option byte) (md : Model) : Prop :=
rh_j rsegs B LLVMF_STK hx [(RH_CID, pos)] lyc Sc W mem md 0 /\
frames Sc = [(RH_CID, pos)] /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rh_kept rsegs hx pos (e01b_env hx pos) W mem (h_regs rsegs hx) /\
garr8 rsegs (mrestrict (w_H W) mem) (h_p rsegs hx) (map (fun b : byte => bv_unsigned b) (h_pl rsegs hx)).

(* FR = 0x80094, __asan_stack_malloc_4 returned: sp = s1 = R, gp, tp, s0 = S, s2 = n, s5 = p, s11 = the shadow
   offset, a0 = F. *)
Definition e01b_fr (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
e01b_base hx pos lyc Sc W mem md /\
getr regs 2 = w64 (e01b_R hx) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e01b_S hx) /\ getr regs 9 = w64 (e01b_R hx) /\ getr regs 18 = w64 (h_n rsegs hx) /\
getr regs 21 = w64 (h_p rsegs hx) /\ getr regs 27 = w64 SHADOW_OFF /\
getr regs 10 = w64 (e01b_F hx pos).

(* HD = 0x80270, the frame's header and shadow written: FR's registers but a0, and s3 = (F >> 3) + K,
   s7 = s10 = F; the frame's 88 shadow bytes hi_shA role_himg_B. *)
Definition e01b_hd (hx : rh_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
e01b_base hx pos lyc Sc W mem md /\
getr regs 2 = w64 (e01b_R hx) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e01b_S hx) /\ getr regs 9 = w64 (e01b_R hx) /\ getr regs 18 = w64 (h_n rsegs hx) /\
getr regs 19 = w64 (shadow_addr (e01b_F hx pos)) /\ getr regs 21 = w64 (h_p rsegs hx) /\
getr regs 23 = w64 (e01b_F hx pos) /\ getr regs 26 = w64 (e01b_F hx pos) /\
getr regs 27 = w64 SHADOW_OFF /\
rl_fsh rsegs (w_H W) mem (e01b_F hx pos) (hi_shA role_himg_B).

(* The input after the flags byte at a state: rest at the cursor e_src (role_build_contract's garr8 form), its
   length, the cursor's bounds, and where it lies: nothing is left, or it is inside one of the entry's blocks (the
   input block). *)
Definition e01b_in (hx : rh_hcx rsegs) (W : world rsegs) (mem : word -> option byte) (e : rl_env) (rest : list byte)
: Prop :=
e_left e = Z.of_nat (length rest) /\
garr8 rsegs (mrestrict (w_H W) mem) (e_src e) (map (fun x : byte => bv_unsigned x) rest) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(e_left e = 0 \/
 exists p n, In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\ p <= e_src e /\
   e_src e + e_left e <= p + req_size n).

(* CALL = 0x524c0, at the `jal` of malloc(19744) 0x802c0 (ra = 0x802c4): the harness journal, the frame, the
   entry's blocks, the geometry, ra / sp / gp / tp, a0 = 19744, every value of C1's list hi_L1 but its first
   (a0 = pp, which only the call gives), the frame's shadow, the flags byte's bound and its tie to the input
   (rh_hdr: e_fl the flags byte, rest = skipn 1 of the input, src / left / len), the carried cells and the input
   after the flags byte. e_pp and e_pod are free here. *)
Definition e01b_call_facts (hx : rh_hcx rsegs) (pos : Z) (e : rl_env) (rest : list byte)
(lyc : alayout) (Sc : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
rh_j rsegs B LLVMF_STK hx [(RH_CID, pos)] lyc Sc W mem md 0 /\
frames Sc = [(RH_CID, pos)] /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rh_geo rsegs hx pos e /\
getr regs 1 = w64 E01B_MALLOC_RA /\ getr regs 2 = w64 (e_R e) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 Layout.PP_SIZE /\
rl_cut rsegs (w_H W) mem regs e (tl (hi_L1 role_himg_B)) /\
rl_fsh rsegs (w_H W) mem (e_F e) (hi_shA role_himg_B) /\
0 <= e_fl e < 256 /\ rh_hdr rsegs hx e rest /\
rh_kept rsegs hx pos e W mem regs /\
e01b_in hx W mem e rest.

(* ======================================== the continuations ======================================== *)
Definition e01b_from_fr (hx : rh_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos lyc Sc W regs mem md, e01b_fr hx pos lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01B_FR regs mem md) POST.
Definition e01b_from_hd (hx : rh_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos lyc Sc W regs mem md, e01b_hd hx pos lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01B_HD regs mem md) POST.
Definition e01b_from_call (hx : rh_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos e rest lyc Sc W regs mem md, e01b_call_facts hx pos e rest lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01B_MALLOC regs mem md) POST.

(* ======================================== the four parts ======================================== *)
Definition e01b_ent_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01b_from_fr hx POST ->
SRr rsegs (h_W rsegs hx) (cfg_at rsegs RH_ENTRY (h_regs rsegs hx) (h_mem rsegs hx) (h_md rsegs hx)) POST.
Definition e01b_pro_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01b_from_hd hx POST -> e01b_from_fr hx POST.
Definition e01b_hdr_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01b_from_call hx POST -> e01b_from_hd hx POST.
Definition e01b_call_stmt : Prop :=
forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> rh_from_C1 rsegs B LLVMF_STK hx POST ->
e01b_from_call hx POST.

(* The four parts compose into S_E01. *)
Lemma e01b_chain : e01b_ent_stmt -> e01b_pro_stmt -> e01b_hdr_stmt -> e01b_call_stmt ->
S_E01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros HE HP HH HC hx POST Hb HK.
exact (HE hx POST Hb (HP hx POST Hb (HH hx POST Hb (HC hx POST Hb HK)))).
Qed.

(* The allocation trace of the malloc(pp) call site (return address 0x802c4): the trace the allocator records is
   its own return pc, then 0x802c4, then the harness's return address when the entry frame is chained. *)
Definition e01b_trace_stmt : Prop :=
forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
raZ regsT = E01B_MALLOC_RA ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
End b.
