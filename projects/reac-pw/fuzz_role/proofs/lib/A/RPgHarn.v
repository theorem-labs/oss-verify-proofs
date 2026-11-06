(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): THE HARNESS-LEVEL CUTS of
   the walk of LLVMFuzzerTestOneInput (0x7ff88, 11308 bytes) and the statements of the three segments that are not
   lib/A/RPgCSpec.v's two fixed middle contracts: S_E01 (ENTRY -> K80194), the malloc(pod) step C2 -> C3
   (0x820c0 -> 0x820c4) and S_X01 (K82478 -> the return). Statement text only: no function is proved here.

   WHY THIS FILE. The whole run is chained in this order:
     ENTRY --S_E01--> K80194 = C1 --role_build_contract--> C2 --malloc(pod)--> C3 --role_check_contract--> C4
     = K82478 --S_X01--> return.
   The two middle contracts are fixed (RPgCSpec.v rl_seg_pre / rl_seg_post at RPgImgA.role_himg_A). The cuts below
   are what the three other segments deliver or assume at the four boundaries, chosen so that the chaining
   (lib/A/RPgTop.v) derives each next premise from what the previous segment gave:
   - every cut is stated relative to the harness's ENTRY state (the record rh_hcx) and its journal from there
     (rh_j: FP = [], own = the frame for locals, k events so far), as rl_seg_pre's journal is;
   - a cut states only what the chaining cannot derive. Left out on purpose: rl_seg_pre's static conjuncts (the
     registered globals' and the strings' shadow, the read-only cells, rom_view, the real frame's checked cells,
     arodata_okP), which the chaining re-derives at C1 and C3 from AR and the journal (rh_static_law, the journal's
     image clause); the fresh-block facts ~ In pp / ~ In pod of the entry's blocks, which follow from AR's block
     disjointness and the appended block list; frames S' = [(3, pos)], which the journal gives from frames S = [];
     and the presence of the frame's bytes and shadow, which AR_frames_law gives at every state;
   - what must survive from K80194 to K82478 across both middle contracts and the malloc call is carried by the
     contracts' "every byte outside the callees' stack and the write set is kept" clauses and the malloc rule's
     acall_kept: the 13 callee-saved words the prologue stores at [S - 0x68, S) (ra at S - 8, s0 at S - 16, ...,
     s11 at S - 0x68: `sd ra,0x198(sp)` 0x7ff90 .. `sd s11,0x138(sp)` 0x7ffc0 after `addi sp,sp,-0x1a0`) and the
     frame's flag pointer word at F + 0x1f8 (the class-3 frame law's last word; the release stores 0 through it at
     0x824b0 .. 0x824b4). Both are rh_kept, over RPgBase's own cell form rl_at (LCell).
   - the frame for locals is F = frame_addr of the ENTRY layout (class 3, position pos): frame_addr and flag_addr
     read only ly_F, which every journal's layout_le keeps (YG0f.v layout_le), so one value serves every cut.
   - the run's quantities are RPgBase.rl_env; S_E01 chooses e at K80194, when pod does not exist yet, so e_pod is
     free there; from C3 on the chaining uses rh_env_pod e pod (C2's lists do not read XPod). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the harness's pcs ============================================ *)
Definition RH_ENTRY : Z := 0x7ff88.     (* `addi sp,sp,-0x1a0` *)
Definition RH_C1 : Z := 0x80194.        (* K80194, `bnez a0` after malloc(pp): hi_c1 role_himg_A *)
Definition RH_C2 : Z := 0x820c0.        (* the `jal` of malloc(pod): hi_c2 role_himg_A *)
Definition RH_C3 : Z := 0x820c4.        (* `beqz a0` after it returns: hi_c3 role_himg_A *)
Definition RH_C4 : Z := 0x82478.        (* K82478, `mv a0,s2` after check_code returns: hi_c4 role_himg_A *)
(* the frame for locals: class 3 (`addi a0,zero,0x1a0` 0x7fff4, `jal __asan_stack_malloc_3` 0x7fff8) *)
Definition RH_CID : Z := 3.
(* the real frame below the entry sp S: R = (S - 0x1a0) & -32 (0x7ff88, 0x7ffc8, 0x7ffcc) *)
Definition RH_RSZ : Z := 0x1a0.
(* the events the whole run records: malloc(pp), malloc(pod), free(pod), free(pp) *)
Definition RH_EV : Z := 4.

Lemma rh_pcs_himg : hi_c1 role_himg_A = RH_C1 /\ hi_c2 role_himg_A = RH_C2 /\ hi_c3 role_himg_A = RH_C3 /\
  hi_c4 role_himg_A = RH_C4 /\ hi_cid role_himg_A = RH_CID /\ hi_rsz role_himg_A = RH_RSZ.
Proof. repeat split; reflexivity. Qed.

(* The 13 callee-saved registers in the order of their save slots S - 8, S - 16, ..., S - 0x68. *)
Definition rh_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* The save slots as RPgBase cells: S - 8 - 8 j holds the entry value of the j-th register. *)
Definition rh_saves_L (regs0 : bvmap 5 word) : list (rl_loc * Z) :=
  map (fun j => (LCell XS (- 8 - 8 * Z.of_nat j), bv_unsigned (getr regs0 (nth j rh_saved_regs 0%bv)))) (seq 0 13).
(* The cells carried from K80194 to K82478: the saves, and the frame's flag pointer word at F + 0x1f8. *)
Definition rh_cells (regs0 : bvmap 5 word) (fl : Z) : list (rl_loc * Z) :=
  rh_saves_L regs0 ++ [(LCell XF 0x1f8, fl)].

(* The run's quantities with the pod block filled in (S_E01 picks e before malloc(pod) runs). *)
Definition rh_env_pod (e : rl_env) (pod : Z) : rl_env :=
  RLEnv (e_S e) (e_R e) (e_F e) (e_pp e) pod (e_len e) (e_fl e) (e_src e) (e_left e).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* the read-only range and the harness constants of RPgCSpec.rl_lib_contract_x (image A: RPgLib.RO_LO / RO_HI and
   the relocated frame's ACfn.RA_LLVMF / A_EMPTY / EV_LIB / LIVE_LIB / LLVMF_STK) *)
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ============================== the harness's entry ============================== *)
Record rh_hcx := RHCx {
h_ly : alayout; h_S : astate; h_W : world segs; h_regs : bvmap 5 word; h_mem : word -> option byte; h_md : Model;
h_p : Z; h_n : Z; h_pl : list byte }.

(* What every harness-level segment may use of the entry: RPgCSpec.rl_lib_pre_x without the parts only the
   final leaf reads (asink_none, the fd and fs facts, ameta_inv, the meter) and without its float clause (which
   S_X01, running at the float state M02 returns, must not mention). *)
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

(* The geometry: S the entry sp, R the 32-aligned base of the real frame, F the class-3 frame at pos. *)
Definition rh_geo (hx : rh_hcx) (pos : Z) (e : rl_env) : Prop :=
e_S e = spZ (h_regs hx) /\ e_R e = 32 * ((e_S e - RH_RSZ) / 32) /\ e_F e = frame_addr (h_ly hx) RH_CID pos.

(* The carried cells (the 13 saves, the flag pointer) at a state. *)
Definition rh_kept (hx : rh_hcx) (pos : Z) (e : rl_env) (W' : world segs) (mem' : word -> option byte)
(regs' : bvmap 5 word) : Prop :=
Forall (fun f => rl_at segs (w_H W') mem' regs' e (fst f) (snd f))
(rh_cells (h_regs hx) (flag_addr (h_ly hx) RH_CID pos)).

(* role_build_contract's input premises at rest (RPgCSpec.v role_build_contract, after rl_cut). *)
Definition rh_input (W' : world segs) (mem' : word -> option byte) (e : rl_env) (rest : list byte) : Prop :=
e_left e = Z.of_nat (length rest) /\ e_len e = rl_len rest /\
garr8 segs (mrestrict (w_H W') mem') (e_src e) (map (fun x : byte => bv_unsigned x) rest) /\
range_addressable (aview segs (w_H W') mem') SHADOW_OFF (e_src e) (e_left e) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(0 < e_left e -> shadow_hull_vis (aview segs (w_H W') mem') (e_src e) (e_left e)) /\
(forall a, e_src e <= a < e_src e + e_left e ->
 ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ rl_inw e (hi_w1 role_himg_A) a /\ ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)).

(* ============================== K80194 (C1): what S_E01 delivers ==============================
   The frame taken (own = [(3, pos)]), malloc(pp) done (one event, the block appended), sp = R, the prologue's
   frame shadow, the C1 values (RPgImgA hi_L1), the input after the flags byte (rh_input at some rest), and the
   carried cells. *)
Definition rh_cut_C1 (hx : rh_hcx) (pos : Z) (e : rl_env) (rest : list byte)
(ly1 : alayout) (S1 : astate) (W1 : world segs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
rh_j hx [(RH_CID, pos)] ly1 S1 W1 mem1 md1 1 /\
ablocks B ly1 S1 = ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE)] /\
getr regs1 2 = w64 (e_R e) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
rh_geo hx pos e /\
rl_fsh segs (w_H W1) mem1 (e_F e) role_A_shA /\
e_pp e <> 0 /\ 0 <= e_fl e < 256 /\
rl_cut segs (w_H W1) mem1 regs1 e (hi_L1 role_himg_A) /\
rh_input W1 mem1 e rest /\
rh_kept hx pos e W1 mem1 regs1.
Definition rh_at_C1 (hx : rh_hcx) : world segs -> config -> Prop :=
fun W1 c1 => exists pos e rest ly1 S1 regs1 mem1 md1,
c1 = cfg_at segs RH_C1 regs1 mem1 md1 /\ rh_cut_C1 hx pos e rest ly1 S1 W1 regs1 mem1 md1.
(* S_E01: the prologue, the frame (option byte 1, __asan_stack_malloc_3(416)), its header and
   shadow, the flags byte and the cursor, malloc(19744). *)
Definition rh_S_E01_stmt : Prop :=
forall hx : rh_hcx, rh_base hx ->
SRr segs (h_W hx) (cfg_at segs RH_ENTRY (h_regs hx) (h_mem hx) (h_md hx)) (rh_at_C1 hx).

(* ============================== C2: what the chaining gives the malloc(pod) step ==============================
   role_build_contract's post at C2 (the journal still at one event, the C2 values hi_L2, sp / gp / tp as at C1)
   with the carried cells and the request's bounds (8 <= len <= 5440, RPgSiteA.rl_len_bounds). *)
Definition rh_cut_C2 (hx : rh_hcx) (pos : Z) (e : rl_env)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
rh_j hx [(RH_CID, pos)] ly2 S2 W2 mem2 md2 1 /\
Permutation (ablocks B ly2 S2) (ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE)]) /\
getr regs2 2 = w64 (e_R e) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
rh_geo hx pos e /\ 8 <= e_len e <= 5440 /\
rl_cut segs (w_H W2) mem2 regs2 e (hi_L2 role_himg_A) /\
rh_kept hx pos e W2 mem2 regs2.
(* What the step leaves at C3: the malloc rule's post (YC5d.v amalloc04_rule) at the returned pod, with the
   callee-saved registers of C2 kept (the `jal` changes only ra) and a0 = pod. *)
Definition rh_at_C3 (hx : rh_hcx) (pos : Z) (e : rl_env)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
: world segs -> config -> Prop :=
fun W3 c3 => exists pod ly3 S3 regs3 mem3 md3,
c3 = cfg_at segs RH_C3 regs3 mem3 md3 /\
rh_j hx [(RH_CID, pos)] ly3 S3 W3 mem3 md3 2 /\
4096 <= pod /\ getr regs3 10 = w64 pod /\
(forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) /\
frames S3 = frames S2 /\ ablocks B ly3 S3 = ablocks B ly2 S2 ++ [(pod, e_len e)] /\
acall_kept segs B ly2 S2 W2 mem2 W3 mem3 (e_R e - ASTACK) (e_R e) (fun a => pod <= a < pod + req_size (e_len e)).
(* The malloc(pod) step: the `jal` at 0x820c0 and the call (a0 = len + (len == 0) = len). *)
Definition rh_S_C23_stmt : Prop :=
forall (hx : rh_hcx) pos e ly2 S2 W2 regs2 mem2 md2,
rh_base hx -> rh_cut_C2 hx pos e ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs RH_C2 regs2 mem2 md2) (rh_at_C3 hx pos e ly2 S2 W2 regs2 mem2).

(* ============================== K82478 (C4): what S_X01 assumes ==============================
   role_check_contract's post at C4 (the C4 values hi_L4, the role granule in scope: role_A_shB) with two events,
   both blocks appended and fresh, and the carried cells. The float state is the Section's: S_X01 is used at the
   float state M02 returns at (it executes no float instruction and its callees keep the float state). *)
Definition rh_cut_C4 (hx : rh_hcx) (pos : Z) (e : rl_env)
(ly4 : alayout) (S4 : astate) (W4 : world segs) (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) : Prop :=
rh_j hx [(RH_CID, pos)] ly4 S4 W4 mem4 md4 2 /\
Permutation (ablocks B ly4 S4) (ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)]) /\
~ In (e_pp e, Layout.PP_SIZE) (ablocks B (h_ly hx) (h_S hx)) /\ ~ In (e_pod e, e_len e) (ablocks B (h_ly hx) (h_S hx)) /\
getr regs4 2 = w64 (e_R e) /\ getr regs4 3 = w64 (as_gp B) /\ getr regs4 4 = w64 (as_tp B) /\
rh_geo hx pos e /\ 8 <= e_len e <= 5440 /\ e_pp e <> 0 /\ e_pod e <> 0 /\
rl_cut segs (w_H W4) mem4 regs4 e (hi_L4 role_himg_A) /\
rl_fsh segs (w_H W4) mem4 (e_F e) role_A_shB /\
rh_kept hx pos e W4 mem4 regs4.
(* The return: knock's rt_post (APgRt.v) in role's terms: at RA_LLVMF, the journal from the entry closed (own = [],
   at most the four events), the callee-saved registers restored, a0 = 0, the entry's blocks again. *)
Definition rh_ret (hx : rh_hcx) : world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
rh_j hx [] ly' S' W' mem' md' k /\ k <= RH_EV /\
aregs_preserved (h_regs hx) regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B (h_ly hx) (h_S hx)).
(* S_X01: free(pod), free(pp), role's granule := 0xf8, F[0] := 0x45e0360e, __asan_set_shadow_f5(s3,
   64), the flag byte := 0, a0 = 0 and the epilogue. *)
Definition rh_S_X01_stmt : Prop :=
forall (hx : rh_hcx) pos e ly4 S4 W4 regs4 mem4 md4,
rh_base hx -> rh_cut_C4 hx pos e ly4 S4 W4 regs4 mem4 md4 ->
SRr segs W4 (cfg_at segs RH_C4 regs4 mem4 md4) (rh_ret hx).

(* ============================== the static facts of rl_seg_pre ==============================
   The shadow of the registered globals and of the strings, the read-only cells and every read-only byte, at any
   state AR accepts with the read-only data as in the image. They are static facts of the symbols B (the start-up's
   const cells and zero-shadow ranges, AR's am_const / al_zshadow, and the owned read-only bytes pinned as const
   cells), not facts a cut can carry: a global's shadow byte and an owned read-only byte are aowned, and the
   allocator's post keeps no aowned byte (YG0d.v acall_post; scene's P_LLVMFuzzerTestOneInput.v Section h ruling).
   The chaining takes this law at the two middle contracts' starts. *)
Definition rh_static_law : Prop :=
forall ly S (W : world segs) mem md,
AR segs B ly S W mem md -> arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
Forall (fun g => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs role_himg_A) /\
Forall (fun s => rl_cstr segs (w_H W) mem (fst s) (snd s)) (hi_strs role_himg_A) /\
rl_ro_cells segs (w_H W) mem (hi_cells role_himg_A) /\
rom_view segs W mem.

End c.
End b.
