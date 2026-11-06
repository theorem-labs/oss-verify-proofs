(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgHarn.v at 3c7e900fc63 and the harness section
   of proofs/reac-pw/fuzz_rate/lib/AU/RtPgSegB.v at 24c66d54276 (its lines 1265-1523) for reac-pw/fuzz_role image B
   (fuzz_role.asan-ubsan): image B's pcs, frame class, real-frame size and flag word and the record lib/AU/RPgImgA.v
   role_himg_B; the cuts and the segment statements in fuzz_rate image B's continuation form (rh_common, rh_from_C1
   .. rh_from_C4, S_E01 / S_M01 / S_M02 / S_X01, rh_S_C23_stmt, rh_seg_chain) with role's one-byte header in place of
   rate's seven, two allocations in place of three, and no third middle segment. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): THE HARNESS-LEVEL CUTS of
   the walk of LLVMFuzzerTestOneInput (0x80020, 10848 bytes, 2712 instructions), the malloc(pod) step and the four
   segment statements S_E01 / S_M01 / S_M02 / S_X01 (lib/Prog/LLVMFuzzerTestOneInput_c.v's names, in its
   continuation form: "the continuation of the exit cut -> the continuation of the entry cut"). Statement text only:
   proves no function (kind: statement text).

   WHY THIS FILE. The whole run is chained in this order:
     ENTRY --S_E01--> C1 --role_build_contract--> C2 --malloc(pod)--> C3 --role_check_contract--> C4 --S_X01--> return,
   and S_M01 = C1 -> C3 (the build, then the malloc(pod) step rh_S_C23_stmt), S_M02 = C3 -> C4. The two middle
   contracts are fixed (lib/A/RPgCSpec.v rl_seg_pre / rl_seg_post at RPgImgA.role_himg_B). Each harness cut is a
   self-contained state relative to the harness's ENTRY state (the record rh_hcx) and its journal from there (rh_j:
   FP = [], own = the frame for locals, k events so far): the frame F = frame_addr of the ENTRY layout (class 4,
   position pos), the run's quantities e with the flags byte and the input cursor tied to the input bytes (rh_hdr),
   the blocks made so far (appended to the entry's and not among them), the cut's values (role_himg_B hi_L1 ..
   hi_L4), the frame's shadow, and the carried cells.
   - Left out on purpose: rl_seg_pre's static conjuncts (the registered globals' and the strings' shadow, the
     read-only cells, rom_view, the real frame's checked cells, arodata_okP), which the chaining re-derives at C1 and
     C3 from AR and the journal (rh_static_law, the journal's image clause); and the presence of the frame's bytes and
     shadow, which AR_frames_law gives at every state.
   - What must survive from C1 to C4 across the two middle contracts and the malloc call is carried by the contracts'
     "every byte outside the callees' stack and the write set is kept" clauses and the malloc rule's acall_kept: the
     13 callee-saved words the prologue stores at [S - 0x68, S) (ra at S - 8, s0 at S - 16, ..., s11 at S - 0x68:
     `sd ra,0x1f8(sp)` 0x80028 .. `sd s11,0x198(sp)` 0x80058 after `addi sp,sp,-0x200`) and the frame's flag pointer
     word at F + 0x3f8 (the class-4 frame law's last word; the release reads it at 0x825a8 through s7, which 0x82588
     reloads from R+0x20, and stores 0 through it at 0x825ac). Both are rh_kept, over RPgBase's cell form rl_at
     (LCell). R+0x20 = F itself is a value of hi_L2 .. hi_L4.
   - frame_addr and flag_addr read only ly_F, which every journal's layout_le keeps (YG0f.v layout_le), so one F
     serves every cut.
   - C4 follows the float-changing parse and pod_nearest: it takes the cut's own float state with a zero rounding
     mode; so does the return. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the harness's pcs ============================================ *)
Definition RH_ENTRY : Z := 0x80020.     (* `addi sp,sp,-0x200` *)
Definition RH_RET : Z := 0x82600.       (* `ret` *)
Definition RH_C1 : Z := 0x802c4.        (* `bnez a0` after malloc(pp) (`jal` 0x802c0): hi_c1 role_himg_B *)
Definition RH_C2 : Z := 0x82164.        (* the `jal` of malloc(pod), a0 = len + (len == 0): hi_c2 role_himg_B *)
Definition RH_C3 : Z := 0x82168.        (* `beqz a0` after it returns: hi_c3 role_himg_B *)
Definition RH_C4 : Z := 0x82570.        (* `mv a0,s2` after check_code returns (`jal` 0x8256c), before the free(pod)
                                          `jal` 0x82574: hi_c4 role_himg_B *)
(* the frame for locals: class 4 (`addi a0,zero,0x2c0` 0x8008c, `jal __asan_stack_malloc_4` 0x80090) *)
Definition RH_CID : Z := 4.
(* the real frame below the entry sp S: R = (S - 0x200) & -32 (0x80020, 0x80060, 0x80064) *)
Definition RH_RSZ : Z := 0x200.
(* the events the whole run records: malloc(pp), malloc(pod), free(pod), free(pp) *)
Definition RH_EV : Z := 4.

Lemma rh_pcs_himg : hi_c1 role_himg_B = RH_C1 /\ hi_c2 role_himg_B = RH_C2 /\ hi_c3 role_himg_B = RH_C3 /\
  hi_c4 role_himg_B = RH_C4 /\ hi_cid role_himg_B = RH_CID /\ hi_rsz role_himg_B = RH_RSZ.
Proof. repeat split; reflexivity. Qed.

(* The 13 callee-saved registers in the order of their save slots S - 8, S - 16, ..., S - 0x68 (0x80028 .. 0x80058;
   restored 0x825c8 .. 0x825f8). *)
Definition rh_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* The save slots as RPgBase cells: S - 8 - 8 j holds the entry value of the j-th register. *)
Definition rh_saves_L (regs0 : bvmap 5 word) : list (rl_loc * Z) :=
  map (fun j => (LCell XS (- 8 - 8 * Z.of_nat j), bv_unsigned (getr regs0 (nth j rh_saved_regs 0%bv)))) (seq 0 13).
(* The cells carried from C1 to C4: the saves, and the frame's flag pointer word at F + 0x3f8. *)
Definition rh_cells (regs0 : bvmap 5 word) (fl : Z) : list (rl_loc * Z) :=
  rh_saves_L regs0 ++ [(LCell XF 0x3f8, fl)].

(* The run's quantities with the pod block filled in (the malloc(pod) step's prover picks the C3 quantities from the
   C2 ones). *)
Definition rh_env_pod (e : rl_env) (pod : Z) : rl_env :=
  RLEnv (e_S e) (e_R e) (e_F e) (e_pp e) pod (e_len e) (e_fl e) (e_src e) (e_left e).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* the read-only range and the harness constants of RPgCSpec.rl_lib_contract_x (image B: lib/AU/RPgLib.v RO_LO /
   RO_HI and lib/AU/YCfn.v's RA_LLVMF / A_EMPTY / EV_LIB / LIVE_LIB / LLVMF_STK) *)
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ============================== the harness's entry ============================== *)
Record rh_hcx := RHCx {
h_ly : alayout; h_S : astate; h_W : world segs; h_regs : bvmap 5 word; h_mem : word -> option byte; h_md : Model;
h_p : Z; h_n : Z; h_pl : list byte }.

(* What every harness-level segment may use of the entry: RPgCSpec.rl_lib_pre_x without the parts only the final
   leaf reads (asink_none, the fd and fs facts, ameta_inv, the meter) and without its float clause (which the segments
   after the parse, running at the float state it returns, must not mention). *)
Definition rh_base (hx : rh_hcx) : Prop :=
afn_pre segs B LLVMF_STK (h_ly hx) (h_S hx) (h_W hx) (h_regs hx) (h_mem hx) (h_md hx) [] /\
raZ (h_regs hx) = RA_LLVMF /\
getr (h_regs hx) 10 = w64 (h_p hx) /\ getr (h_regs hx) 11 = w64 (h_n hx) /\
((h_n hx = 0 /\ h_p hx = A_EMPTY) \/ (0 < h_n hx < 2 ^ 26 /\ In (h_p hx, h_n hx) (ablocks B (h_ly hx) (h_S hx)))) /\
h_n hx = Z.of_nat (length (h_pl hx)) /\
garr8 segs (mrestrict (w_H (h_W hx)) (h_mem hx)) (h_p hx) (map (fun b : byte => bv_unsigned b) (h_pl hx)) /\
frames (h_S hx) = [] /\ st_nev (h_S hx) + EV_LIB <= EV_MAX /\ blocks_bytes (h_S hx) + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H (h_W hx)) (h_mem hx)).

(* The harness's journal from its entry: no footprint, own = the frames taken, k events. *)
Definition rh_j (hx : rh_hcx) (own : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world segs)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx) own ly' S' W' mem' md' k.

(* The geometry: S the entry sp, R the 32-aligned base of the real frame, F the class-4 frame at pos. *)
Definition rh_geo (hx : rh_hcx) (pos : Z) (e : rl_env) : Prop :=
e_S e = spZ (h_regs hx) /\ e_R e = 32 * ((e_S e - RH_RSZ) / 32) /\ e_F e = frame_addr (h_ly hx) RH_CID pos.

(* The carried cells (the 13 saves, the flag pointer) at a state. *)
Definition rh_kept (hx : rh_hcx) (pos : Z) (e : rl_env) (W' : world segs) (mem' : word -> option byte)
(regs' : bvmap 5 word) : Prop :=
Forall (fun f => rl_at segs (w_H W') mem' regs' e (fst f) (snd f))
(rh_cells (h_regs hx) (flag_addr (h_ly hx) RH_CID pos)).

(* The header (fuzz_role.c:136-142, fuzz.h:37-43: fuzz_u8 reads one byte, or gives 0 and reads nothing when no byte
   is left): flags = byte 0 of the input or 0; pod_build reads the input after it, at p + min(1, n), n - min(1, n)
   of them (0x80274 / 0x802b0 into s4, 0x802a0 / 0x802a8 into s6); the pod's length is pp->len after pod_build of
   those bytes. *)
Definition rh_u8 (pl : list byte) (i : nat) : Z :=
match nth_error pl i with Some b => bv_unsigned b | None => 0 end.
Definition rh_hdr (hx : rh_hcx) (e : rl_env) (rest : list byte) : Prop :=
e_fl e = rh_u8 (h_pl hx) 0 /\
rest = skipn 1 (h_pl hx) /\ e_src e = h_p hx + Z.min 1 (h_n hx) /\ e_left e = h_n hx - Z.min 1 (h_n hx) /\
e_len e = rl_len rest.

(* role_build_contract's input premises at rest (RPgCSpec.v role_build_contract, after rl_cut). *)
Definition rh_input (W' : world segs) (mem' : word -> option byte) (e : rl_env) (rest : list byte) : Prop :=
e_left e = Z.of_nat (length rest) /\
garr8 segs (mrestrict (w_H W') mem') (e_src e) (map (fun x : byte => bv_unsigned x) rest) /\
range_addressable (aview segs (w_H W') mem') SHADOW_OFF (e_src e) (e_left e) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(0 < e_left e -> shadow_hull_vis (aview segs (w_H W') mem') (e_src e) (e_left e)) /\
(forall a, e_src e <= a < e_src e + e_left e ->
 ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ rl_inw e (hi_w1 role_himg_B) a /\ ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)).

(* What every harness cut shares: the journal at k events with the frame for locals as the only frame, the blocks
   made so far (bl, in the order they were made) appended to the entry's and none of them among the entry's, sp = R,
   gp, tp, the geometry, the header tie, the flags byte's bound, the carried cells, and the cut's values. *)
Definition rh_common (hx : rh_hcx) (pos : Z) (e : rl_env) (rest : list byte) (k : Z) (bl : list (Z * Z))
(L : list (rl_loc * rl_x))
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_j hx [(RH_CID, pos)] ly2 S2 W2 mem2 md2 k /\ frames S2 = [(RH_CID, pos)] /\
Permutation (ablocks B ly2 S2) (ablocks B (h_ly hx) (h_S hx) ++ bl) /\
Forall (fun b => ~ In b (ablocks B (h_ly hx) (h_S hx))) bl /\
getr regs2 2 = w64 (e_R e) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
rh_geo hx pos e /\ rh_hdr hx e rest /\ 0 <= e_fl e < 256 /\
rl_cut segs (w_H W2) mem2 regs2 e L /\
rh_kept hx pos e W2 mem2 regs2.

(* ============================== C1: what S_E01 delivers ==============================
   The frame taken, malloc(pp) done (one event, the block appended), the prologue's frame shadow (hi_shA), the C1
   values (hi_L1), and the input after the flags byte (rh_input at rest = skipn 1 of the input). *)
Definition rh_cut_C1 (hx : rh_hcx) (pos : Z) (e : rl_env) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 1 [(e_pp e, Layout.PP_SIZE)] (hi_L1 role_himg_B) ly2 S2 W2 regs2 mem2 md2 /\
e_pp e <> 0 /\ rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shA role_himg_B) /\
rh_input W2 mem2 e rest.
(* ============================== C2: what role_build_contract's post gives the malloc(pod) step ==============
   The C2 values (hi_L2), the prologue's shadow again, pp holding Layout.pp_bytes of the record pod_build made of
   rest, and the request's bounds (8 <= len <= 5440: RPgSiteA's rl_len_bounds). *)
Definition rh_cut_C2 (hx : rh_hcx) (pos : Z) (e : rl_env) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 1 [(e_pp e, Layout.PP_SIZE)] (hi_L2 role_himg_B) ly2 S2 W2 regs2 mem2 md2 /\
e_pp e <> 0 /\ rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shA role_himg_B) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pp e)
(map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest)))).
(* ============================== C3: what the malloc(pod) step delivers ==============================
   Two events, pod appended (len bytes: len >= 8, so the request len + (len == 0) is len), the C3 values (hi_L3), the
   prologue's shadow, pp's bytes kept. *)
Definition rh_cut_C3 (hx : rh_hcx) (pos : Z) (e : rl_env) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 2 [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)] (hi_L3 role_himg_B)
  ly2 S2 W2 regs2 mem2 md2 /\
e_pp e <> 0 /\ e_pod e <> 0 /\ rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shA role_himg_B) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W2) mem2) (e_pp e)
(map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest)))).
(* ============================== C4: what role_check_contract's post gives S_X01 ==============================
   The C4 values (hi_L4), the role cell's granule in scope (hi_shB), at the cut's own float state fx4. *)
Definition rh_cut_C4 (hx : rh_hcx) (fx4 : YK11.FPState) (pos : Z) (e : rl_env) (rest : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
: Prop :=
rh_common hx pos e rest 2 [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)] (hi_L4 role_himg_B)
  ly2 S2 W2 regs2 mem2 md2 /\
e_pp e <> 0 /\ e_pod e <> 0 /\ rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shB role_himg_B) /\
YK0o.frm_zero (@fp_csr fx4).

(* The return: knock's rt_post (APgRt.v) in role's terms: at RA_LLVMF, the journal from the entry closed (own = [],
   at most the four events), the callee-saved registers restored, a0 = 0, the entry's blocks again. The float state
   is the one the configuration carries (S_X01 executes no float instruction; its callees keep the float state). *)
Definition rh_ret (hx : rh_hcx) : world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = @cfg_at fx' segs RA_LLVMF regs' mem' md' /\ YK0o.frm_zero (@fp_csr fx') /\
rh_j hx [] ly' S' W' mem' md' k /\ k <= RH_EV /\
aregs_preserved (h_regs hx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (h_ly hx) (h_S hx)).

(* ============================== the continuations at the harness cuts ============================== *)
Definition rh_from_C1 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C1 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RH_C1 regs2 mem2 md2) POST.
Definition rh_from_C2 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C2 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RH_C2 regs2 mem2 md2) POST.
Definition rh_from_C3 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C3 hx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RH_C3 regs2 mem2 md2) POST.
Definition rh_from_C4 (hx : rh_hcx) (POST : world segs -> config -> Prop) : Prop :=
forall fx4 pos e rest ly2 S2 W2 regs2 mem2 md2, rh_cut_C4 hx fx4 pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx4 segs RH_C4 regs2 mem2 md2) POST.

(* ============================== the segment statements ==============================
   S_E01, ENTRY -> C1: the prologue (`addi sp,sp,-0x200` 0x80020, the probe `sd zero,0(sp)` 0x80024, the saves at
   [S - 0x68, S) 0x80028 .. 0x80058, s0 = S, sp = s1 = R 0x8005c .. 0x80064); K through the GOT cell 0x9aad0 (0x8006c,
   0x80078, 0x80080) and the option byte through the GOT cell 0x9ab28 (0x80070, 0x80074, 0x8007c): it is 1, so
   `beqz a2` 0x80088 falls through: frame_alloc_4(704) 0x8008c / 0x80090, `bnez s7` 0x800a4 taken (the real-stack arm
   0x800a8 .. 0x800c0 is not run); R+0x170 := F (0x800c4); the frame's header (0x800c8 .. 0x800f8) and its 88 shadow
   bytes (0x80104 .. 0x80264); n < 2^26, so `beqz a3` 0x80268 is taken; the flags byte: for n > 0 the
   pointer-overflow test `bltu` 0x8027c (its trap jump 0x80280 is not taken), the instrumented check 0x80284 ..
   0x80294 (slow path 0x8264c), `lbu` 0x80298 and R+0x40 := fl 0x8029c; for n = 0 R+0x40 := 0 (0x802ac);
   malloc(19744) at 0x802c0 with ra = 0x802c4. *)
Definition S_E01 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C1 hx POST ->
SRr segs (h_W hx) (cfg_at segs RH_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) POST.
(* S_M01, C1 -> C3: role_build_contract at role_himg_B (from C1, with rl_seg_pre's static conjuncts from
   rh_static_law), then the malloc(pod) step (rh_S_C23_stmt). *)
Definition S_M01 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C3 hx POST -> rh_from_C1 hx POST.
(* S_M02, C3 -> C4: role_check_contract at role_himg_B. *)
Definition S_M02 : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C4 hx POST -> rh_from_C3 hx POST.
(* S_X01, C4 -> RET: free(pod) 0x82574 (a0 = s2, 0x82570), free(pp) 0x8257c (a0 = s6, 0x82578); role's granule :=
   0xf8 (0x82580 / 0x82584); s7 := R+0x20 (0x82588); F[0] := 0x45e0360e (0x8258c .. 0x82594, F in s10); `beqz s7`
   0x82598 not taken; meta_fill_f5(s3, 128) 0x8259c .. 0x825a4; the flag byte := 0 through F + 0x3f8 (0x825a8 ..
   0x825ac); a0 = 0 (0x825c0) and the epilogue (0x825c4 .. 0x82600). *)
Definition S_X01 : Prop :=
forall (hx : rh_hcx), rh_base hx -> rh_from_C4 hx (rh_ret hx).
Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_M02 /\ S_X01.

(* The malloc step S_M01 adds to its contract. C2 -> C3: the `jal` at 0x82164 with a0 = len + (len == 0) = len
   (`ld s8,0(s6)` 0x82158 or 0x81f28, `seqz a0,s8` 0x8215c, `add a0,s8,a0` 0x82160) and the call. *)
Definition rh_S_C23_stmt : Prop :=
forall (hx : rh_hcx) POST, rh_base hx -> rh_from_C3 hx POST -> rh_from_C2 hx POST.

(* The four statements compose into the whole run: from ENTRY, the return. *)
Lemma rh_seg_chain : seg_lemmas -> forall hx : rh_hcx, rh_base hx ->
SRr segs (h_W hx) (cfg_at segs RH_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) (rh_ret hx).
Proof.
intros (HE & HM1 & HM2 & HX) hx Hb.
exact (HE hx (rh_ret hx) Hb (HM1 hx _ Hb (HM2 hx _ Hb (HX hx Hb)))).
Qed.

(* ============================== the static facts of rl_seg_pre ==============================
   The shadow of the registered globals and of the strings, the read-only cells and every read-only byte, at any
   state AR accepts with the read-only data as in the image. They are static facts of the symbols B (the start-up's
   const cells and zero-shadow ranges, AR's am_const / al_zshadow, and the owned read-only bytes pinned as const
   cells), not facts a cut can carry: a global's shadow byte and an owned read-only byte are aowned, and the
   allocator's post keeps no aowned byte (YG0d.v acall_post). The chaining takes this law at the two middle
   contracts' starts. *)
Definition rh_static_law : Prop :=
forall ly S (W : world segs) mem md,
AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs role_himg_B) /\
Forall (fun s => rl_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs role_himg_B) /\
rl_ro_cells segs (w_H W) mem (hi_cells role_himg_B) /\
rom_view segs W mem.

End c.
End b.
