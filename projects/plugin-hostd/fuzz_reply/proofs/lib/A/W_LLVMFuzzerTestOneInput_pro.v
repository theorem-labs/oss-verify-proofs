(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEG_PRO of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the prologue
   0x840b0-0x842a0 (fuzz_reply.c:671-685), from the entry to the loop head H (or to the shutdown X on an empty input),
   in the form of lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt and of the cgif fake-frame walks
   (proofs/cgif/cgif_file_fuzzer/lib/A/ACk1.v: prologue, stack_malloc, the frame's header and shadow).
   The segment: the frame (320 bytes, sp aligned down to 32, s1 = F), the ASan fake frame of class 1
   (__asan_stack_malloc_1, 128 bytes) with its header and shadow, the size refusal (n >= 2^26) refuted by the
   contract's n < 2^26, the globals' reset (g_client = 3, g_client_broken, g_nfd, g_send_max, g_gone, g_send_dead,
   g_send_eintr = 0), op_add(), and the loop's set-up (the frame slots F+32 .. F+152), to the head 0x842a0, or for
   n = 0 to the shutdown block 0x84bf8.
   lf_seg_pro (the statement of _cut.v's SEG_PRO) is proved here; the pieces are pro_entry (the entry state), the
   walk to __asan_stack_malloc_1 and the fake-frame seat, the global stores and the token run to op_add's entry,
   pro_at_call (op_add's entry state), pro_mid (op_add at its own G, oa_spec_g at G_oa, its journal lifted to G_fr)
   and pro_fin (the loop's set-up 0x84234-0x842a0, the empty-input exit 0x84bf8).
   What this file takes (all Section hypotheses, none proved here):
     LAWS / HG / RINV / LS / the contract parameters - _cut's Section w, verbatim;
     TL, TLF, ML, SMP, FFL - the allocator instance (W_kit.v, W_frame.v); GWL, ERRL - _cut's shared laws;
     ASM1 : astack_malloc_pres at class 1 (W_frame.v; RelocA's AF0s.v stack_malloc1_contract proves it);
     W2_op_add : oa_spec_g at op_add's entry, the text of a working branch 81d480c10a4 lib/A/W_op_add.v, which
       pb_op_add_g proves;
     HEV, HZS, HG_obj, ROM_PIN, SHV_oa - instance facts, in the text of a working branch 825c723c13f
       lib/A/W_LLVMFuzzerTestOneInput_addI.v's zz_HEV, zz_HZS, zz_HGOBJ, zz_ROMPIN and zz_GSHV (G_oa is its ad_G,
       4 * ASRC = 384); HROM_G - _G.v's c_rom_apart at G_fr_c;
     HFP_pro - the entry's relay table and output buffer are live blocks apart from the input and inside fr_FP;
     LS_pro_oa, LS_pro, RI_pro - the allocator-room / model obligations at op_add's call and at the first head. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_G W_LLVMFuzzerTestOneInput_latch.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the segment's addresses (offsets from fr_B0) *)
Definition A_pro : Z := AF_fr_LLVMFuzzerTestOneInput.                    (* 0x840b0 the entry *)
Definition A_pro_ret : Z := AF_fr_LLVMFuzzerTestOneInput + 0x184.        (* 0x84234 after op_add() *)
(* the frame: s1 = F = (sp0 - 320) rounded down to 32; the slots the prologue stores lie in [F + 24, F + 208) *)
Definition pro_F (regs : bvmap 5 word) : Z := (spZ regs - 320) - (spZ regs - 320) mod 32.
(* g_nfd, as W2's op_add contract names it (fuzz_reply.asan 0x5d8820, A_OBJ 29) *)
Definition A_NFD : Z := 0x5d8820.

Section pro.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- _cut's Section w, verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ------------------------------------------------------------------ op_add, as a Section hypothesis *)
(* op_add's contract, the text of a working branch 81d480c10a4 lib/A/W_op_add.v (oa_spec and oa_post, with
   oa_post's last conjunct: errno's view is kept) at PI := PB_fr, and its G-generic form oa_spec_g over
   W_contract.v gx_prog.  W2's pb_op_add_g concludes exactly `oa_spec_g B MT (BASE + AF_fr_op_add)`; the stub is a
   copy until this file takes W_op_add.v. *)
Definition OA_FRAME : Z := 64.
Definition OA_STK : Z := OA_FRAME + RA_STK.
Definition oa_first (os : list Z) : option nat :=
if nth 0 os 0 =? 0 then Some 0%nat
else if nth 1 os 0 =? 0 then Some 1%nat
else if nth 2 os 0 =? 0 then Some 2%nat
else if nth 3 os 0 =? 0 then Some 3%nat else None.
Definition oa_HA (i : nat) : Z := rg_s fr_globals + ASRC * Z.of_nat i.
Definition oa_new_src (fd q : Z) (pj : list byte) : hsrc :=
HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list.
Definition oa_cost : Z := sr_cost MT None + mo_malloc MT APARTIAL + mo_malloc MT ATABLE + mo_free MT.
Definition oa_FP (os : list Z) (T : Z) (es : list rentry) : list (Z * Z) :=
match oa_first os with None => [] | Some _ => ra_FP T es end.
Definition oa_wr (os : list Z) (a : Z) : Prop :=
match oa_first os with
| None => False
| Some i => oa_HA i <= a < oa_HA i + ASRC \/ A_NFD <= a < A_NFD + 4 \/ inG (RA_G fr_globals) a
end.
Definition oa_kept (G : list (Z * Z)) (os : list Z) (W : world segs) (mem : word -> option byte)
(W' : world segs) (mem' : word -> option byte) : Prop :=
forall a, inG G a -> ~ oa_wr os a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Definition oa_post (G : list (Z * Z)) (regs : bvmap 5 word) ly S (W : world segs) (mem : word -> option byte) (md : Model)
(os : list Z) (n0 T : Z) (es : list rentry) : world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_gx segs B G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S W mem md [] ly' S' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ oa_kept G os W mem W' mem' /\ frames S' = frames S /\
match oa_first os with
| None => ly' = ly /\ S' = S /\ W' = W /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - OA_STK <= a < spZ regs) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
| Some i => exists (q T' : Z) (pj : list byte),
    asrc_at B ly' S' W' mem' (oa_HA i) (oa_new_src (100 + n0) q pj) /\
    val_mem segs (arm W' mem') A_NFD 4 (n0 + 1) /\
    arelay_at B fr_globals ly' S' W' mem' T' (es ++ [ra_new (100 + n0)]) /\
    alock_at fr_globals W' mem' false /\
    ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: (q, APARTIAL) :: ablocks B ly S)) \/
     (T <> 0 /\ T' = T /\ Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S))) /\
    mo_le MT S S' oa_cost
end /\
(forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i)).
Definition oa_spec (G : list (Z * Z)) (pc : Z) : Prop :=
forall W ly S regs mem md ch (os : list Z) (n0 T : Z) (es : list rentry),
afn_pre segs B OA_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem segs (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
(forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W mem (oa_HA i)) ->
val_mem segs (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view segs W mem ->
(oa_first os <> None -> (length es < 4)%nat /\ ~ In (100 + n0) (map re_fd es)) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX ->
mo_ok MT S oa_cost ->
SRr segs W (cfg_at segs pc regs mem md) (oa_post G regs ly S W mem md os n0 T es).
Definition oa_spec_g (pc : Z) : Prop := forall G, gx_prog B G -> oa_spec G pc.
Hypothesis W2_op_add : oa_spec_g (BASE + AF_fr_op_add).

(* ------------------------------------------------------------------ the other lanes' facts *)
Hypothesis TL : PALib B.                            (* the allocator instance (W_kit.v) *)
Hypothesis TLF : PALibF B.                          (* its fake-stack fields (W_frame.v) *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM1 : astack_malloc_pres segs B 1.      (* W5's form, W_frame.v; RelocA's AF0s.v proves class 1 *)
Hypothesis FFL : frame_flag_lawP segs B.
(* _cut's two shared facts (W_LLVMFuzzerTestOneInput_cut.v glob_wr_law / errno_law), verbatim *)
Hypothesis GWL : glob_wr_law G_fr.
Hypothesis ERRL : errno_law B.
(* discharged by zz_ERRL B TS, a working branch 825c723c13f
   lib/A/W_LLVMFuzzerTestOneInput_addI.v:242 *)
(* ---- instance facts, in _top.v's text (HEV, HZS: AF0m's ts_errno / ts_zsh, measured in _G.v's header) ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_A.
(* discharged by zz_HEV B TS, a working branch 825c723c13f lib/A/W_LLVMFuzzerTestOneInput_addI.v:51 *)
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* discharged by zz_HZS B TS, a working branch 825c723c13f lib/A/W_LLVMFuzzerTestOneInput_addI.v:55 *)
(* ---- G_fr: it holds the program's 20 objects (_G.v obj_c proves it of G_fr_c), and no read-only byte (_G.v
   c_rom_apart) ---- *)
Hypothesis HG_obj : forall a, inG G_fr_obj a -> inG G_fr a.
(* discharged at G_fr := G_fr_c B by zz_HGOBJ B, a working branch 825c723c13f
   lib/A/W_LLVMFuzzerTestOneInput_addI.v:64 *)
Hypothesis HROM_G : forall a, in_rom segs a -> ~ inG G_fr a.
(* ---- the instance obligation of W_journal.v's rom_out (a working branch 45a3cc9bdd0): an owned read-only byte
   is one of AR's pinned const cells (AF0m pins all 408) ---- *)
Hypothesis ROM_PIN : forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
(* discharged by zz_ROMPIN B TS, a working branch 825c723c13f
   lib/A/W_LLVMFuzzerTestOneInput_addI.v:131 *)
(* ---- op_add's own G (W_op_add.v:165-168, FREE-W8.md (sha256 b75e6b922a31; internal record)), and the one conjunct of gx_prog at it that is not a fact of the
   image: the shadow of its globals is readable in every allocator state ---- *)
Definition G_oa : list (Z * Z) := [(rg_s fr_globals, 384); (A_NFD, 4)] ++ RA_G fr_globals.
Hypothesis SHV_oa : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG G_oa x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* discharged by zz_GSHV B TS, a working branch 825c723c13f
   lib/A/W_LLVMFuzzerTestOneInput_addI.v:187,
   stated at ARM_add's ad_G = [(rg_s fr_globals, 4 * ASRC); (A_NFD, 4)] ++ RA_G fr_globals, which is G_oa
   (4 * ASRC = 384; the two are convertible) *)
(* ---- the entry's surviving blocks (the relay's table g_src and the controller's buffer g_out): apart from the input
   block and inside the entry's footprint fr_FP (_cut.v:124-128) over their REQUEST size, as the cut's ablocks_sep
   (req_size, a Theorem Labs lane's ruling 12:2xZ) and op_add's journal take them.  Conjuncts 2-3 follow from the instance's
   fr_FP (ACfn_cf.fr_FP reads g_src / g_out's ranges from entry memory).  Conjunct 1 (the entry split) needs the
   input block, g_src's table and g_out's buffer to be DISTINCT blocks, which the cut's pre does not state yet
   (a Theorem Labs lane's review 21:5xZ, reported to the cut's owner): it is not a consequence of fr_live_pre. ---- *)
Hypothesis HFP_pro : forall cx T c O mx cap out,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ra_rel B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) T [] ->
  aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c O mx (Z.of_nat (length O)) cap out ->
  (exists rest, Permutation (ablocks B (c_ly cx) (c_S cx))
     (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest)) /\
  (T <> 0 -> forall a, T <= a < T + req_size ATABLE -> inFP (lf_FP fr_FP cx) a) /\
  (forall b, In b (aout_blks cap out) -> forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
(* ---- the allocator-state invariant's facts op_add takes, at the state after the fake frame (LS_pro_oa), and the
   cut's two Variables at the first cut point (LS_pro, RI_pro): the model after op_add, k = 0 ---- *)
Hypothesis LS_pro_oa : forall cx (S2 : astate) pos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 oa_cost.
Definition pro_m (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z) : lmod :=
  LM 0 [Some (oa_new_src 100 q pj); None; None; None] T' [ra_new 100] c O 0 cap out 0 1.
Hypothesis RI_pro : forall cx q T' pj c O cap out,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (a Theorem Labs lane 20:4xZ; W8Add's fr_LS_pro, a working branch f57b3e2d0ca
   lib/A/ReplyLS.v:571): the blocks after op_add are given with the entry's split at its table T0 (HFP_pro's first
   conjunct) and relay_add's two cases (T0 = 0: a new table T'; T0 <> 0: T' = T0), so LS's own rest can be built.
   The published premise (a bare disjunction of the two Permutations) gives no such split. *)
Hypothesis LS_pro : forall cx q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT S2 S oa_cost ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  LS cx 0 (pro_m q T' pj c O cap out) ly S.
(* the coverage facts the prologue's global stores take, from HG_obj *)
Lemma pro_cov : forall lo n, rng_inb lo n G_fr_obj = true -> forall a, lo <= a < lo + n -> inG G_fr a.
Proof. intros lo n H a Ha. exact (HG_obj a (rng_cover lo n G_fr_obj H a Ha)). Qed.
Let HG_client := pro_cov (rg_client fr_RG) 4 ltac:(vm_compute; reflexivity).
Let HG_cbroken := pro_cov (rg_client_broken fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_nfd := pro_cov A_NFD 4 ltac:(vm_compute; reflexivity).
Let HG_smax := pro_cov (rg_send_max fr_RG) 8 ltac:(vm_compute; reflexivity).
Let HG_gone := pro_cov (rg_gone fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_sdead := pro_cov (rg_send_dead fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_seintr := pro_cov (rg_send_eintr fr_RG) 1 ltac:(vm_compute; reflexivity).

(* ------------------------------------------------------------------ the image's read-only bytes *)
Definition rom_inb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma rom_inb_ok : forall a, rom_inb a = true -> in_rom segs a.
Proof.
  intros a H. unfold rom_inb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hs|]. split; [exact H0|]. lia.
Qed.
(* a read-only byte reads as the image's, in a memory with the ROM view *)
Lemma pro_rom_mbyte : forall (W : world segs) mem a, rom_view segs W mem -> in_rom segs a ->
  mbyte segs (arm W mem) a = seg_rom segs (Z_to_bv 64 a).
Proof.
  intros W mem a HR Ha. pose proof (HR a Ha) as E. unfold aview in E. unfold arm.
  destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b1|]; destruct (seg_rom segs (Z_to_bv 64 a)) as [b2|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Definition rom_vmb (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => rom_inb (a + Z.of_nat k) &&
    match seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) with
    | Some b => Z.eqb (bv_unsigned b) (le_byte v n k) | None => false end) (seq 0 n).
Lemma rom_vmb_ok : forall (W : world segs) mem a n v, rom_view segs W mem -> rom_vmb a n v = true ->
  val_mem segs (arm W mem) a n v.
Proof.
  intros W mem a n v HR H k Hk. unfold rom_vmb in H. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_seq; lia)). apply andb_prop in H as [H1 H2].
  rewrite (pro_rom_mbyte W mem _ HR (rom_inb_ok _ H1)).
  destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate H2].
  apply Z.eqb_eq in H2. f_equal. apply bv_eq. rewrite H2. symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold le_byte. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
(* the jump table's words, from the ROM view *)
Lemma pro_jt : forall (W : world segs) mem, rom_view segs W mem -> jt_rom W mem.
Proof.
  intros W mem HR i Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
    apply (rom_vmb_ok W mem _ _ _ HR); vm_compute; reflexivity.
Qed.

(* ------------------------------------------------------------------ bytes a run or a call keeps *)
Lemma pro_kept_frame : forall E rs (W : world segs) m m' a,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  abyte_kept W m W m' a.
Proof.
  intros E rs W m m' a HF Ha Hn. split.
  - exact (aview_kept_out (PI := PB_fr) E rs (w_H W) m m' HF a Ha Hn).
  - intros Hw. unfold writable_at, arm in *.
    assert (Ex : mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a))
      by (apply HF; rewrite unsigned_lit_small by lia; exact Hn).
    unfold wview in *. rewrite Ex. exact Hw.
Qed.
(* a byte the loaded image holds writable is writable in every memory (_G.v wr_of_seg, for any memory) *)
Lemma pro_wr_any : forall (m : word -> option byte) a,
  wview segs (fun _ => None) (Z_to_bv 64 a) <> None -> writable_at segs m a.
Proof.
  intros m a Hw. unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [cbv iota; discriminate | exact Hw].
Qed.
(* rom_out at a G that misses every read-only byte: the other conjuncts are G's-independent *)
Lemma pro_rom_out : forall G, (forall a, in_rom segs a -> ~ inG G a) -> rom_out segs B G.
Proof.
  intros G HnG a Ha. split; [exact (HnG a Ha)|]. split; [exact (ROM_PIN a Ha)|]. split.
  - rewrite HEV. intros He. apply (rom_apart_ok segs [(TFIB_ERRNO_A, 4)] a ltac:(vm_compute; reflexivity) Ha).
    apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact He.
  - intros Hh. assert (HA : rom_apart segs [(AOFL_HEAD, 8)] = true) by (vm_compute; reflexivity).
    apply (rom_apart_ok segs _ a HA Ha). apply inG_cons. left. unfold in_zr. cbn [fst snd]. exact Hh.
Qed.
Lemma pro_rom_out_fr : rom_out segs B G_fr.
Proof. exact (pro_rom_out G_fr HROM_G). Qed.

(* ------------------------------------------------------------------ op_add's G *)
Lemma G_oa_obj : forall a, inG G_oa a -> inG G_fr_obj a.
Proof.
  apply inG_sub. unfold G_oa, RA_G. cbn [app].
  repeat (apply Forall_cons; [intros a Ha; refine (rng_cover_zr _ _ G_fr_obj _ a Ha); vm_compute; reflexivity|]).
  apply Forall_nil.
Qed.
Lemma G_oa_fr : forall a, inG G_oa a -> inG G_fr a.
Proof. intros a Ha. exact (HG_obj a (G_oa_obj a Ha)). Qed.
Lemma G_oa_rt : gx_rt B G_oa.
Proof.
  intros a Ha. rewrite HEV.
  pose proof (rng_all_in (fun x => negb ((TFIB_ERRNO_A <=? x) && (x <? TFIB_ERRNO_A + 4)) &&
    negb ((VAL (A_OBJ 0) <=? x) && (x <? VAL (A_OBJ 0) + 8)) &&
    negb ((VAL (A_OBJ 32) <=? x) && (x <? VAL (A_OBJ 32) + 8))) G_oa a ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H1, H2, H3.
  split; [|split]; intros [Hx1 Hx2];
    [ rewrite (proj2 (Z.leb_le _ _) Hx1), (proj2 (Z.ltb_lt _ _) Hx2) in H1; discriminate H1
    | rewrite (proj2 (Z.leb_le _ _) Hx1), (proj2 (Z.ltb_lt _ _) Hx2) in H2; discriminate H2
    | rewrite (proj2 (Z.leb_le _ _) Hx1), (proj2 (Z.ltb_lt _ _) Hx2) in H3; discriminate H3 ].
Qed.
Lemma G_oa_prog : gx_prog B G_oa.
Proof.
  split; [exact (gx_ok_sub segs B G_oa G_fr G_oa_fr HG)|].
  split; [exact G_oa_rt|].
  split; [apply pro_rom_out; intros a Ha; exact (rom_apart_ok segs G_oa a ltac:(vm_compute; reflexivity) Ha)|].
  split.
  { intros a Ha.
    pose proof (rng_all_in (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end)
      G_oa a ltac:(vm_compute; reflexivity) Ha) as H.
    cbv beta in H. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate H]. }
  split; [intros a Ha m; apply pro_wr_any; apply (segwb_ok segs);
          exact (rng_all_in (segwb segs) G_oa a ltac:(vm_compute; reflexivity) Ha)|].
  exact SHV_oa.
Qed.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run (PL := PL_fr) (PI := PB_fr) B LAWS.
Let RUNP := SRr_run_pi_AJ (PL := PL_fr) (PI := PB_fr) B LAWS.
Let RUNX := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTOX := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ------------------------------------------------------------------ the entry state *)
Definition Bx : sv := SOff 33 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the frame's bytes the prologue writes: the slot sp0 - 320 (`sd zero,0(sp)`) and the saved registers
   [sp0 - 104, sp0), both through sp0 (atom 2); the slots [F + 24, F + 208), through F (atom 34) *)
Definition pr_zero : YP09.region := YP09.mkRegion (Some 2%nat) (-320) (-312) (-320) (-312) [].
Definition pr_save : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition pr_F : YP09.region := YP09.mkRegion (Some 34%nat) 24 208 24 208 [].
Definition pro_regions0 : smem :=
  [ pr_zero; pr_save; pr_F; got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32 ].
(* `andi sp, sp, -32` lands on F (atom 34), by the alias *)
Definition pro_alias : sv * sv := (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32)), SOff 34 0).
Definition pro_facts0 : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF 0x10000 0x5fb000 2);
            (33%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5) ] [] [pro_alias].
Definition ss_pro0 : sstate := mkSS A_pro sr_atoms pro_regions0 None pro_facts0.
Definition pro_extra (regs : bvmap 5 word) : list word := map (Z_to_bv 64) [as_uar_cell B; SB; pro_F regs].
(* the globals the prologue resets, each stored through the auipc register of its hi slot j (0x841e0-0x8422c) *)
Definition pr_g (j : nat) (off w : Z) : YP09.region := YP09.mkRegion (Some (A_HI j)) off (off + w) off (off + w) [].
Definition pro_gregs : smem :=
  [ pr_g 67 (-512) 4; pr_g 68 1528 1; pr_g 69 1588 4; pr_g 70 1616 8; pr_g 71 1636 1; pr_g 72 1660 1;
    pr_g 73 1684 1 ].
(* the image values the prologue names, at the pinned placement *)
Lemma pro_vals :
  VAL (A_HI 67) = 0xa21e0 /\ VAL (A_HI 68) = 0x5d81e8 /\ VAL (A_HI 69) = 0x5d81ec /\ VAL (A_HI 70) = 0x5d81f0 /\
  VAL (A_HI 71) = 0x5d81fc /\ VAL (A_HI 72) = 0x5d8204 /\ VAL (A_HI 73) = 0x5d820c /\
  VAL (A_HI 74) = HI_G_NSRC /\ VAL (A_HI 75) = HI_G_SRC /\ VAL (A_HI 76) = HI_G_NOUT /\
  VAL (A_HI 77) = 0x5d8254 /\ VAL (A_HI 78) = 0x10258 /\
  VAL (A_OBJ 22) = 0x5d88e0 /\ VAL (A_OBJ 25) = 0x1239d /\ VAL (A_OBJ 26) = 0x10320 /\
  VAL (A_OBJ 0) = 0x9d9d0 /\ VAL (A_OBJ 32) = 0xa60b8.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* a sign-extended byte store leaves its low byte (the fake frame's shadow poison) *)
Lemma pro_chunk1 : forall E m n b cs lo hi wlo whi od z,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (SLit z))) cs ->
  mbyte segs m (b + od) = Some (byte_of_word (Z_to_bv 64 z) 0).
Proof.
  intros E m n b cs lo hi wlo whi od z (_ & _ & _ & Hcs) Hn Hin.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. specialize (Hck 0 ltac:(cbn; lia)).
  destruct Hck as (bb & Hc & Hm). cbn [YP09.r_base base_val YP09.c_off YP09.c_val cbyte sv_denot] in Hc, Hm.
  rewrite Hn, Z.add_0_r in Hm. injection Hc as <-. exact Hm.
Qed.
(* the fake frame's shadow poison, read off its region (16 sign-extended byte stores) *)
Definition fs_z (j : nat) : Z :=
  if (j <? 4)%nat then 18446744073709551601 else if (j <? 10)%nat then 18446744073709551608
  else 18446744073709551603.
Lemma pro_shadow_garr8 : forall E m n b cs lo hi wlo whi,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  (forall j, (j < 16)%nat -> In (YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit (fs_z j)))) cs) ->
  garr8 segs m b fake_shadow.
Proof.
  intros E m n b cs lo hi wlo whi HR Hb HF j Hj. cbn [length fake_shadow] in Hj.
  assert (Hz : forall j, (j < 16)%nat ->
    byte_of_word (Z_to_bv 64 (fs_z j)) 0 = Z_to_bv 8 (le_byte (nth j fake_shadow 0) 1 0) /\
    0 <= nth j fake_shadow 0 < 256).
  { clear. intros j Hj. do 16 (destruct j as [|j]; [split; [apply bv_eq; vm_compute; reflexivity | cbn; lia]|]). lia. }
  destruct (Hz j Hj) as [Hz1 Hz2]. split; [|exact Hz2].
  intros k Hk. assert (k = 0)%nat as -> by lia. rewrite Z.add_0_r.
  rewrite (pro_chunk1 E m n b cs lo hi wlo whi (Z.of_nat j) (fs_z j) HR Hb (HF j Hj)). rewrite Hz1. reflexivity.
Qed.
(* the saved registers, read off the stack region through sp0 (W_op_add.v oa_saved_of_region) *)
Lemma pro_saved_of_region : forall E m spv cs lo hi wlo whi (regs : bvmap 5 word),
  region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = spv ->
  (forall r, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))) ->
  Forall (fun p => In (YP09.mkChunk (- fst p) (CVal 8 (SOff (Z.to_nat (snd p)) 0))) cs) saved_regs ->
  forall o r, In (o, r) saved_regs -> val_mem segs m (spv - o) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
  intros E m spv cs lo hi wlo whi regs HR Hsp EA HIn o r Hp.
  rewrite Forall_forall in HIn. pose proof (HIn _ Hp) as Hin. cbn [fst snd] in Hin.
  assert (Hr : 0 <= r < 32)
    by (unfold saved_regs in Hp; cbn [In] in Hp;
        repeat (destruct Hp as [Hp | Hp]; [injection Hp as <- <-; lia|]); destruct Hp).
  replace (spv - o) with (spv + (- o)) by lia. change 8%nat with (N.to_nat 8).
  apply (field_of_region (PI := PB_fr) E m 2 spv cs lo hi wlo whi (- o) 8 (SOff (Z.to_nat r) 0) _ HR Hsp Hin).
  - cbn [sv_denot]. rewrite EA by lia. rewrite Z2Nat.id by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HB. change (bv_modulus 64) with (2 ^ 64) in HB.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
Qed.

Lemma pro_F_facts : forall sp0, sp0 mod 16 = 0 ->
  (sp0 - 320) - (sp0 - 320) mod 32 = sp0 - 320 \/ (sp0 - 320) - (sp0 - 320) mod 32 = sp0 - 336.
Proof.
  intros sp0 H. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hb.
  pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
  rewrite H in D2. lia.
Qed.
Lemma pro_F_al : forall x, (x - x mod 32) mod 32 = 0.
Proof. intros x. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. Qed.

Lemma pro_entry : forall W ly S regs mem md ch n,
  afn_pre segs B LLVMF_STK ly S W regs mem md ch -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (pro_extra regs))) ss_pro0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_pro)) mem (seg_rom segs)))
  /\ sh_ok segs Bx [] (Eimg (Ereg regs (pro_extra regs))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S regs mem md ch n HPRE H11 Rn.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
  pose proof (palf_uar_img B TLF) as HuR. pose proof (palf_uar_al B TLF) as HuA. pose proof (palf_sep B TLF) as HSEP.
  cbn [zseps zseps_from fst snd] in HSEP.
  set (F := pro_F regs).
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (pro_extra regs))). pose proof pa_B_ok as HBASE.
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E11 : ew E 11 = getr regs 11) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
  { intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
  split.
  - unfold ss_pro0, A_pro. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite UF. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
          [cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 32)) 0 8 (SOff 33 0) SB);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff 32 0) (as_uar_cell B));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
      * rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
    + apply pairwise_disjoint_of_extents.
      unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. cbn [base_val]. rewrite Usp, UF.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert HFv HspR Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HguR HuR HSEP. clear.
      unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [pro_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, UF, E11, H11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert HFv HFal HspR Hal16 Rn HuR HuA. clear. unfold SB. intros.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [pro_facts0 f_alias alias_ok pro_alias]. split; [|exact I].
        assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
        apply U_inj. rewrite U_SAlu, (U_atom_off E 2 (spZ regs) (-320) E2'), (U_atom E 34 F E34) by lia.
        rewrite U_SLit. cbn [zalu_raw].
        assert (Hlo : 0 <= spZ regs + -320 < 2 ^ 64) by (destruct HspR as [HspR1 HspR2]; destruct HFv as [HFv | HFv]; rewrite HFv in HspR1; lia).
        change (zcanon (-32)) with (2 ^ 64 - 2 ^ 5). rewrite (land_neg_pow2_u64 (spZ regs + -320) 5 Hlo ltac:(lia)).
        assert (EF : spZ regs + -320 - (spZ regs + -320) mod 2 ^ 5 = F) by reflexivity.
        rewrite EF. apply zcanon_id. unfold M64. destruct HspR as [HspR1 HspR2]. destruct HFv as [HFv | HFv]; lia.
  - unfold sh_ok. constructor.
Qed.

(* ------------------------------------------------------------------ state tactics *)
(* keep the regions idxs of HS's state *)
Ltac pro_keep HS idxs :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (YP03.pick (ss_mem ssx) idxs) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_submem (PI := PB_fr) Ex ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* make region i read-only *)
Ltac pro_ro HS i :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  let HSk := fresh "HSk" in
  pose proof (ast_ok_pi_set_region (PI := PB_fr) Ex ssx msx i r (set_window r 0 0) HS eq_refl eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow sg Ex _ r 0 0 (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) ltac:(intros o Ho; lia)))
    as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* rewrite every image atom's value in the goal, then compute each named image value *)
Ltac pro_val :=
  repeat match goal with |- context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv; clear Hv end.
Ltac pro_img HEI :=
  repeat match goal with |- context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia))
    end end;
  pro_val.
Ltac pro_imgh HEI H :=
  repeat match type of H with context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia)) in H
    end end;
  repeat match type of H with context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv in H; clear Hv end.
(* add the store region of global hi slot j, offset off, width w, whose bytes HGx puts in G_fr *)
Ltac pro_addg HS HEI j off w HGx :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_region Ex ssx msx (pr_g j off w) HS eq_refl
    ltac:(unfold region_ok, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          pro_img HEI; split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; cbn [ms_mem restrict mkst]; apply GWL; apply HGx; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          repeat match goal with H : bv_unsigned (ew ?E ?a) = _ |- context [bv_unsigned (ew ?E ?a)] => rewrite H end;
          pro_img HEI;
          unfold SB, off_img in *; repeat split; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* pin image atom n to its value in HS's facts (the token run's static check reads a store region's base off them) *)
Ltac pro_addf HS HEI n :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let v := eval vm_compute in (VAL n) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_fact Ex ssx msx n (mkAF v v 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia)); pro_val;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.

(* ------------------------------------------------------------------ the frame's numbers *)
Lemma pro_Fb : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  CEIL8 + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) - 352 <= lf_F cx /\
  spZ (c_regs cx) <= 2 ^ 47 /\ lf_F cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
  intros cx (_ & HPRE0).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  pose proof (pro_F_al (spZ (c_regs cx) - 320)) as Hal32. rewrite <- HF32 in Hal32.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, LLVMF_STK in *; lia).
  split; [exact HFlo|]. split; [lia|]. split; [lia|]. split; [unfold LLVMF_STK in *; lia|].
  split; [exact Hal32 | exact Hal16].
Qed.
Lemma abyte_kept_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof. intros W1 W2 W3 m1 m2 m3 a [H1 H2] [H3 H4]. split; [rewrite H3; exact H1 | intros Hw; exact (H4 (H2 Hw))]. Qed.
(* the frame's bytes are present wherever the journal from the entry holds *)
Lemma pro_frame_wr : forall cx own ly3 S3 k (W : world segs) mem md,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a.
Proof.
  intros cx own ly3 S3 k W mem md (_ & _ & (memS & HJi & _) & _) a Ha. rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* the frame and the fake frame after op_add (aframe_at but for F+96 and the slots the loop's set-up stores) *)
Definition pro_fr (cx : lfcx) (FF : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in
  (forall o r, In (o, r) saved_regs -> sv8 W mem (sp0 - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) /\
  sv8 W mem (F + 24) 0xa21e0 /\ sv8 W mem (F + 48) 0x5d8204 /\ sv8 W mem (F + 56) 0x5d820c /\
  sv8 W mem (F + 64) 0x5d81fc /\ sv8 W mem (F + 72) 0x5d81f0 /\ sv8 W mem (F + 80) FF /\ sv8 W mem (F + 88) FF /\
  sv8 W mem (F + 184) FF /\
  sv8 W mem FF 0x41b58ab3 /\ sv8 W mem (FF + 8) 0x1239d /\ sv8 W mem (FF + 16) 0x840b0 /\ awr W mem FF 128 /\
  garr8 segs (arm W mem) (SB + FF / 8) fake_shadow /\ awr W mem (SB + FF / 8) 16.
(* the registers op_add returns with (callee-saved, as the prologue left them) *)
Definition pro_regs (cx : lfcx) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 21 = w64 (c_n cx) /\ getr regs 22 = w64 (c_p cx) /\ getr regs 24 = w64 (SB + FF / 8) /\
  getr regs 26 = w64 SB /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

(* ------------------------------------------------------------------ 0x84234, back from op_add *)
(* the loop's set-up stores F+32 and F+96 .. F+152 through s1 (atom 9), reads FF at F+88 and the /10 multiplier
   at 0x10320 (.rodata, the listing's object 26) *)
Definition pr2_32 : YP09.region := YP09.mkRegion (Some 9%nat) 32 40 32 40 [].
Definition pr2_88 : YP09.region := YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SOff 33 0))].
Definition pr2_96 : YP09.region := YP09.mkRegion (Some 9%nat) 96 160 96 160 [].
Definition pr2_div : YP09.region := YP09.mkRegion (Some (A_OBJ 26)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit DIV10))].
Definition pro2_regions : smem := [pr2_32; pr2_88; pr2_96; pr2_div].
Definition pro2_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 (2 ^ 47) 5) ] [] [].
Definition ss_pro2 : sstate := mkSS A_pro_ret sr_atoms pro2_regions None pro2_facts.
Definition Bx2 : sv := SOff 32 0.
Definition pro2_extra (FF : Z) : list word := map (Z_to_bv 64) [SB; FF].
Lemma pro_entry2 : forall (W : world segs) regs mem F FF,
  getr regs 9 = w64 F -> CEIL8 <= F -> F + 208 <= 2 ^ 47 -> F mod 32 = 0 -> 4096 <= FF <= 2 ^ 47 -> FF mod 32 = 0 ->
  val_mem segs (arm W mem) (F + 88) 8 FF -> val_mem segs (arm W mem) 0x10320 8 DIV10 ->
  (forall a, F + 32 <= a < F + 160 -> writable_at segs (arm W mem) a) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (pro2_extra FF))) ss_pro2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)))
  /\ sh_ok segs Bx2 [] (Eimg (Ereg regs (pro2_extra FF))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F FF H9 HF0 HF1 HFal HFF HFFa HV88 HVD HWR. rewrite restrict_mkst_fx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := Eimg (Ereg regs (pro2_extra FF))).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 FF)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E26 : ew E (A_OBJ 26) = Z_to_bv 64 0x10320).
  { subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    pose proof pro_vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PVO26 & _). rewrite PVO26.
    reflexivity. }
  assert (VB9 : base_val E (Some 9%nat) = F)
    by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (VB26 : base_val E (Some (A_OBJ 26)) = 0x10320)
    by (cbn [base_val]; rewrite E26; apply unsigned_lit_small; lia).
  split.
  - unfold ss_pro2. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold pro2_regions, pr2_32, pr2_88, pr2_96, pr2_div.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite VB9. split; [unfold CEIL8 in *; lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply HWR. lia.
      * rewrite VB9. split; [unfold CEIL8 in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 88 8 (SOff 33 0) FF);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact HV88].
      * rewrite VB9. split; [unfold CEIL8 in *; lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply HWR. lia.
      * rewrite VB26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ 0x10320 0 8 (SLit DIV10) DIV10); [reflexivity | unfold DIV10; zside | zside |].
        rewrite Z.add_0_r. exact HVD.
    + apply pairwise_disjoint_of_extents.
      unfold pro2_regions, pr2_32, pr2_88, pr2_96, pr2_div, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB9, VB26.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold CEIL8 in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [pro2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E32, E33, !unsigned_lit_small by (unfold SB, CEIL8 in *; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
      repeat match goal with |- _ /\ _ => split end; unfold CEIL8 in *; lia.
  - unfold sh_ok. constructor.
Qed.
(* aframe_at, from the facts after op_add, the slot F+96 and (full) the loop's set-up slots *)
Lemma pro_aframe : forall cx (full : bool) FF (W : world segs) mem,
  pro_fr cx FF W mem -> sv8 W mem (lf_F cx + 96) (SB + FF / 8) ->
  (full = true -> sv8 W mem (lf_F cx + 32) (rg_s fr_RG) /\ sv8 W mem (lf_F cx + 104) HI_G_NOUT /\
     sv8 W mem (lf_F cx + 112) (SB + rg_s fr_RG / 8) /\ sv8 W mem (lf_F cx + 120) HI_G_NSRC /\
     sv8 W mem (lf_F cx + 128) (rg_s fr_RG + 4) /\ sv8 W mem (lf_F cx + 136) DIV10 /\
     sv8 W mem (lf_F cx + 152) (SB + (rg_s fr_RG + 4) / 8)) ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a) ->
  lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) - 352 <= lf_F cx ->
  aframe_at cx full FF W mem.
Proof.
  intros cx full FF W mem (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW)
    H96 HFULL HWR HF1 HF2.
  unfold aframe_at. cbv zeta.
  split; [exact HSV|]. split; [intros i Hi; apply HWR; unfold LLVMF_STK; lia|].
  split; [exact H24|]. split; [exact H48|]. split; [exact H56|]. split; [exact H64|]. split; [exact H72|].
  split; [exact H80|]. split; [exact H88|]. split; [exact H96|]. split; [exact H184|]. split; [exact HFULL|].
  split; [exact HH0|]. split; [exact HH8|]. split; [exact HH16|]. split; [exact HFW|]. split; [exact HSH | exact HSW].
Qed.
(* region i of HS's state, as region_ok *)
Ltac pro_rgn HS i HR :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) as HR end.
(* the registers the loop's set-up keeps *)
Definition pro_kept : list (bv 5) := [2; 3; 4; 8; 9; 21; 22; 24; 26]%bv.
(* a symbolic value read as a number, and the shadow address of a + c in the shadow matcher's form (W2's oa_sv_lit /
   oa_sh_den, W_op_add.v:693-707, which this file does not Require) *)
Lemma pro_sv_lit : forall E e v, U E e = zcanon v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. apply bv_eq. unfold U in H. rewrite H, Z_to_bv_unsigned. apply zcanon_wrap. Qed.
Lemma pro_sh_den : forall E (bx g : nat) sb a c,
  ew E bx = Z_to_bv 64 sb -> ew E g = Z_to_bv 64 a -> 0 <= sb < 2 ^ 62 -> 0 <= a < 2 ^ 62 -> 0 <= a + c < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff bx 0) (SAlu ALU_SRL (SOff g c) (SLit 3))) = Z_to_bv 64 (sb + (a + c) / 8).
Proof.
  intros E bx g sb a c Hb Hg Hsb Ha Hac. apply pro_sv_lit. rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E bx sb Hb) by lia. rewrite (U_atom_off E g a c Hg) by lia. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (a + c) / 8 <= a + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite (zcanon_id ((a + c) / 8)) by (unfold M64; lia). reflexivity.
Qed.

(* ------------------------------------------------------------------ 0x84234-0x842a0: the loop's set-up *)
Lemma pro_fin : forall cx (W : world segs) regs mem md ly3 S3 k m fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  pro_fr cx (frame_addr ly3 1 fpos) W mem -> pro_regs cx (frame_addr ly3 1 fpos) regs ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m -> lm_k m = 0 -> ainput_at B cx ly3 S3 W mem -> rom_view segs W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx 0 m ly3 S3 -> RINV cx 0 m ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)) md)
    (fun W' c' => INV_H B G_fr fr_FP LS RINV cx 0 W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx W regs mem md ly3 S3 k m fpos HB HJ HFR HRG HFLG HMOD Hk0 HIN HRV HSEP HLS HRI.
  pose proof (pro_Fb cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (Hn26 : 0 <= c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  set (FF := frame_addr ly3 1 fpos) in *. set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  destruct (al_frames _ _ LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFFal & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1, HFFal.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof HFR as (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R21 & R22 & R24 & R26 & R3 & R4).
  assert (HDIV : val_mem segs (arm W mem) 0x10320 8 DIV10)
    by (apply (rom_vmb_ok W mem _ _ _ HRV); vm_compute; reflexivity).
  assert (HWR : forall a, F + 32 <= a < F + 160 -> writable_at segs (arm W mem) a)
    by (intros a Ha; apply (pro_frame_wr cx _ _ _ _ W mem md HJ); unfold sp0 in *; lia).
  destruct (pro_entry2 W regs mem F FF R9 ltac:(lia) ltac:(lia) HFal ltac:(lia) HFFal H88 HDIV HWR) as [HS SHOK].
  remember (Eimg (Ereg regs (pro2_extra FF))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (pro2_extra FF)) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (E21 : ew E 21 = Z_to_bv 64 (c_n cx))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E24 : ew E 24 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E33 : ew E 33 = Z_to_bv 64 FF)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  clear HE.
  pose proof pro_vals as (PV67 & PV68 & PV69 & PV70 & PV71 & PV72 & PV73 & PV74 & PV75 & PV76 & PV77 & PV78 &
    PVO22 & PVO25 & PVO26 & PVO0 & PVO32).
  assert (VI : forall j v, VAL (A_HI j) = v -> (A_HI j < A_LIM)%nat -> 0 <= v < 2 ^ 64 -> ew E (A_HI j) = Z_to_bv 64 v).
  { intros j v Hv Hj Hr. apply bv_eq. rewrite (HEI (A_HI j) ltac:(unfold A_HI, A_TEXT in *; lia)).
    rewrite unsigned_lit_small by exact Hr. exact Hv. }
  (* every fact of the cut but the slots the set-up stores, for any memory that keeps the bytes outside them *)
  assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8) by (rewrite HEV; unfold TFIB_ERRNO_A, CEIL8; lia).
  assert (KEEPF : forall mf, (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
      abyte_kept W mem W mf a) ->
    amodel_at B ly3 S3 W mf m /\ ainput_at B cx ly3 S3 W mf /\ rom_view segs W mf /\ jt_rom W mf /\
    pro_fr cx FF W mf /\ sv8 W mf (FF + 120) (flag_addr ly3 1 fpos)).
  { intros mf KO.
    assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mf a)
      by (intros a Ha; apply KO; unfold CEIL8 in *; lia).
    assert (HRVf : rom_view segs W mf) by exact (lt_rom_kept W W mem mf HRV KL).
    split; [exact (lt_amodel_kept B LAWS ly3 S3 W mem md W mf m HAR HMOD (proj1 Herr) (proj2 Herr) KL)|].
    split; [exact (lt_ainput_kept B LAWS cx ly3 S3 W mem md W mf HAR HIN (eq_sym HlenP) KL)|].
    split; [exact HRVf|]. split; [exact (pro_jt W mf HRVf)|].
    assert (KH : forall a v, (forall x, a <= x < a + 8 -> abyte_kept W mem W mf x) -> sv8 W mem a v -> sv8 W mf a v)
      by (intros a v Hk Hv; exact (lt_sv8_kept W W mem mf a v Hk Hv)).
    split; [|apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFLG]].
    split; [intros o r Hor; apply KH; [|exact (HSV o r Hor)]; intros x Hx;
            unfold saved_regs in Hor; cbn [In] in Hor;
            repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; apply KO; unfold sp0 in *; lia|]);
            destruct Hor|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H24]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H48]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H56]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H64]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H72]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H80]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H88]|].
    split; [apply KH; [intros x Hx; apply KO; unfold sp0 in *; lia | exact H184]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH0]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH8]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH16]|].
    split; [apply (akept_awr W mem W mf); [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFW]|].
    split; [apply (akept_garr8 W mem W mf); [intros x Hx; apply KL; cbn [length fake_shadow] in Hx;
            pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia
            | exact HSH]|].
    apply (akept_awr W mem W mf); [intros x Hx; apply KL;
      pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia | exact HSW]. }
  paj_run_tok RUNX HS HJ SHOK Bspan.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
        first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
    destruct Hin'. }
  clear HF.
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
    assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
      abyte_kept W m1 W m2 a) end.
  { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
    destruct Hin'. }
  clear HFr.
  psrr_branch_tok RUNX BR HS SHOK Bspan.
  - (* beqz s5: an empty input goes to the shutdown block *)
    assert (Hn0 : c_n cx = 0).
    { rewrite branch_eq_U, (U_atom E 21 (c_n cx) E21), U_lit in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
    paj_run_to_tok RUNTOX HS HJ SHOK Bspan AF_LLVM_exit.
    { intros a (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
          first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
      destruct Hin'. }
    clear HF.
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
      assert (KO2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
        abyte_kept W m1 W m2 a) end.
    { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
      destruct Hin'. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (pro2_extra FF) pro_kept HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
    pro_rgn HS 2%nat HR96.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
      apply SRr_ret; right; exists rf, mf, df, 0 end.
    split; [reflexivity|].
    lazymatch type of KO2 with forall a, _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
      destruct (KEEPF m2 (fun a H0 H1 H2 => abyte_kept_trans W W W _ _ _ a (KO1 a H0 H1 H2) (KO2 a H0 H1 H2)))
        as (HMODf & HINf & HRVf & HJTf & HFRf & HFLf) end.
    split; [exact HJTf|].
    exists [(1, fpos)], ly3, S3, k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|].
    split.
    { apply (pro_aframe cx false FF W _ HFRf).
      - pose proof (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
                 reflexivity) ltac:(unfold SB in *; zside) ltac:(zside)) as V96.
        exact V96.
      - intros Hf. discriminate Hf.
      - exact (pro_frame_wr cx _ _ _ _ W _ _ HJ).
      - lia.
      - lia. }
    split; [exact HFLf|].
    split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
    split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
    unfold lregs_X.
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite Q18; change 355%nat with (A_HI 75); apply VI; [exact PV75 | cbv; lia | unfold HI_G_SRC; lia]|].
    split; [rewrite Q23; change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia]|].
    split; [rewrite Q25; change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia]|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite Hk0; lia | unfold OPS_MAX; lia].
  - (* the loop head *)
    assert (Hn0 : c_n cx <> 0).
    { rewrite branch_eq_U, (U_atom E 21 (c_n cx) E21), U_lit in Hc by lia. apply Z.eqb_neq in Hc. exact Hc. }
    paj_run_to_tok RUNTOX HS HJ SHOK Bspan AF_LLVM_head.
    { intros a (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
          first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
      destruct Hin'. }
    clear HF.
    lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
      assert (KO2 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 40) -> ~ (F + 96 <= a < F + 160) ->
        abyte_kept W m1 W m2 a) end.
    { intros a Ha H1 H2. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
      lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
      cbn [In] in Hin'.
      repeat (destruct Hin' as [<- | Hin'];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
      destruct Hin'. }
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (pro2_extra FF) pro_kept HS HAE
      ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
    prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (27%bv : bv 5) Q27.
    pro_rgn HS 0%nat HR32. pro_rgn HS 2%nat HR96.
    assert (Hgs : rg_s fr_RG = 0x5d88e0) by (vm_compute; reflexivity).
    assert (E263 : ew E (A_OBJ 22) = Z_to_bv 64 (rg_s fr_RG))
      by (apply bv_eq; rewrite (HEI (A_OBJ 22) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
          rewrite unsigned_lit_small by (rewrite Hgs; lia); rewrite PVO22, Hgs; reflexivity).
    change (A_OBJ 22) with 263%nat in E263.
    pose proof (pro_sh_den E 26 263 SB (rg_s fr_RG) 0 E26 E263 ltac:(unfold SB; lia) ltac:(lia) ltac:(lia)) as D112.
    pose proof (pro_sh_den E 26 263 SB (rg_s fr_RG) 4 E26 E263 ltac:(unfold SB; lia) ltac:(lia) ltac:(lia)) as D152.
    rewrite Z.add_0_r in D112.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
      apply SRr_ret; left; exists rf, mf, df end.
    split; [reflexivity|].
    lazymatch type of KO2 with forall a, _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
      destruct (KEEPF m2 (fun a H0 H1 H2 => abyte_kept_trans W W W _ _ _ a (KO1 a H0 H1 H2) (KO2 a H0 H1 H2)))
        as (HMODf & HINf & HRVf & HJTf & HFRf & HFLf) end.
    split; [exact HJTf|].
    exists [(1, fpos)], ly3, S3, k, m, fpos.
    split; [exact HJ|]. split; [reflexivity|].
    split.
    { apply (pro_aframe cx true FF W _ HFRf).
      - exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
                 reflexivity) ltac:(unfold SB in *; zside) ltac:(zside)).
      - intros _.
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 32 40 32 40 32 8 (SOff 263 0) (rg_s fr_RG) HR32 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E263, unsigned_lit_small, Z.add_0_r by lia;
                 reflexivity) ltac:(zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 104 8 (SOff 356 0) HI_G_NOUT HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                 change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia])
          ltac:(unfold HI_G_NOUT; zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 112 8
          (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 263 0) (SLit 3))) (SB + rg_s fr_RG / 8) HR96 U9
          ltac:(cbn [In]; tauto) D112 ltac:(rewrite Hgs; unfold SB; change (6129888 / 8) with 766236; zside)
          ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 120 8 (SOff 354 0) HI_G_NSRC HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
                 change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia])
          ltac:(unfold HI_G_NSRC; zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 128 8 (SOff 263 4) (rg_s fr_RG + 4) HR96 U9
          ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E263, unsigned_lit_small by lia; reflexivity)
          ltac:(zside) ltac:(zside))|].
        split; [exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 136 8 (SLit DIV10) DIV10 HR96 U9
          ltac:(cbn [In]; tauto) eq_refl ltac:(unfold DIV10; zside) ltac:(zside))|].
        exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 160 96 160 152 8
          (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 263 4) (SLit 3))) (SB + (rg_s fr_RG + 4) / 8) HR96 U9
          ltac:(cbn [In]; tauto) D152 ltac:(rewrite Hgs; unfold SB; change ((6129888 + 4) / 8) with 766236; zside)
          ltac:(zside)).
      - exact (pro_frame_wr cx _ _ _ _ W _ _ HJ).
      - lia.
      - lia. }
    split; [exact HFLf|].
    split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
    split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
    unfold lregs_H, lregs_common.
    split.
    { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
      split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
      split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
      split; [rewrite Q18; change 355%nat with (A_HI 75); apply VI; [exact PV75 | cbv; lia | unfold HI_G_SRC; lia]|].
      split; [rewrite Q19, E33, unsigned_lit_small by lia; reflexivity|].
      split; [rewrite Q20; reflexivity|].
      split; [rewrite Q23; change 354%nat with (A_HI 74); apply VI; [exact PV74 | cbv; lia | unfold HI_G_NSRC; lia]|].
      split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
      split; [rewrite Q25; change 356%nat with (A_HI 76); apply VI; [exact PV76 | cbv; lia | unfold HI_G_NOUT; lia]|].
      split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
      split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
      rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
    split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
    split; [rewrite (KR 21%bv ltac:(cbv; tauto)), Hk0, Z.sub_0_r; exact R21|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)), Hk0, Z.add_0_r; exact R22|].
    split; [rewrite Q27; reflexivity|].
    split; [unfold OPS_MAX; lia|].
    rewrite Hk0. lia.
Qed.

(* ------------------------------------------------------------------ op_add's call: what the callee keeps *)
(* the live blocks are pairwise distinct (W_gesture_end.v ablocks_nodup), and two distinct ones are apart *)
Lemma pro_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma pro_blk_disj : forall ly S (W : world segs) mem md x y, AR segs B ly S W mem md ->
  In x (ablocks B ly S) -> In y (ablocks B ly S) -> x <> y ->
  fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
  intros ly S W mem md x y HAR Hx Hy Hne.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hp Hx Hy. induction (ablocks B ly S) as [|b l IH]; intros Hp Hx Hy; [destruct Hx|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
  - exfalso. exact (Hne eq_refl).
  - pose proof (Hf _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hy)) as H.
    unfold zdisjoint in H. cbn [fst snd] in H. exact H.
  - pose proof (Hf _ (in_map (fun b => (fst b, req_size (snd b))) _ _ Hx)) as H.
    unfold zdisjoint in H. cbn [fst snd] in H. lia.
  - exact (IH Hp Hx Hy).
Qed.
(* the cells the prologue keeps from the entry to the call: the four sources, the stream's counters, g_wake[1],
   g_thread_up, g_listen and relay_add's globals *)
Definition G_keep : list (Z * Z) :=
  [(rg_s fr_globals, 384); (rg_nout fr_globals, 8); (rg_capout fr_globals, 8); (rg_out fr_globals, 8);
   (rg_wake fr_globals + 4, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] ++ RA_G fr_globals.
(* the cells op_add keeps: the stream's, g_gone, g_wake[1], g_thread_up, g_listen *)
Definition G_pst : list (Z * Z) :=
  [(rg_send_max fr_globals, 8); (rg_nout fr_globals, 8); (rg_capout fr_globals, 8); (rg_out fr_globals, 8);
   (rg_client fr_globals, 4); (rg_client_broken fr_globals, 1); (rg_send_dead fr_globals, 1);
   (rg_send_eintr fr_globals, 1); (rg_gone fr_globals, 1); (rg_wake fr_globals + 4, 4); (AG_THREAD_UP, 1);
   (AG_LISTEN, 4)].
Lemma G_obj_wr : forall a, inG G_fr_obj a -> forall m, writable_at segs m a.
Proof.
  intros a Ha m. apply pro_wr_any. apply (segwb_ok segs).
  exact (rng_all_in (segwb segs) G_fr_obj a ltac:(vm_compute; reflexivity) Ha).
Qed.
Lemma G_obj_err : forall a, inG G_fr_obj a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HEV.
  pose proof (rng_all_in (fun x => negb ((TFIB_ERRNO_A <=? x) && (x <? TFIB_ERRNO_A + 4))) G_fr_obj a
    ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. apply negb_true_iff in H. intros [H1 H2].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in H. discriminate H.
Qed.
Lemma G_obj_rng : forall a, inG G_fr_obj a -> 0x10000 <= a < 0x5fb000.
Proof.
  intros a Ha.
  pose proof (rng_all_in (fun x => (0x10000 <=? x) && (x <? 0x5fb000)) G_fr_obj a
    ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma G_sub_obj : forall G, forallb (fun r => rng_inb (fst r) (snd r) G_fr_obj) G = true ->
  forall a, inG G a -> inG G_fr_obj a.
Proof.
  intros G H. apply inG_sub. rewrite Forall_forall. intros [lo n] Hr a Ha. rewrite forallb_forall in H.
  exact (rng_cover_zr lo n G_fr_obj (H _ Hr) a Ha).
Qed.
Lemma G_keep_obj : forall a, inG G_keep a -> inG G_fr_obj a.
Proof. apply G_sub_obj. vm_compute. reflexivity. Qed.
Lemma G_pst_obj : forall a, inG G_pst a -> inG G_fr_obj a.
Proof. apply G_sub_obj. vm_compute. reflexivity. Qed.
Lemma G_pst_oa : forall a, inG G_pst a -> ~ inG G_oa a.
Proof.
  intros a Ha HO. pose proof (rng_all_in (fun x => negb (inGb G_oa x)) G_pst a ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. apply negb_true_iff in H. apply inGb_false in H. exact (H HO).
Qed.
(* what a callee taken at its own G keeps (W2's oa_call_keep / _blk / _hi, W_op_add.v:245-293), and the caller's
   fake frames (the journal's frame clause) *)
Lemma pro_call_img : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
  forall a, in_img segs a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
  pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Him Hno He ltac:(apply fp_spares_closed; exact Hsk)).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma pro_call_blk : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
  ~ inFP FP (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  rewrite (F2 p n j H0 H1 Hj Hfp).
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
  apply (aview_gagree segs G' (w_H W0) m0 memS (p + j) HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  exact (blk_img segs B LAWS ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
Lemma pro_call_hi : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  gx_ok segs B G' ->
  ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  rewrite (F1 a Ha Hno).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
  pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
Lemma pro_call_frm : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
  ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  forall cid pos a, In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G' a -> aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx cid pos a Hin Hr Hfp Ha HnG.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hfp).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* a closed slot's open flag reads 0 *)
Lemma pro_closed_vm : forall (W : world segs) mem HA, asrc_closed W mem HA -> val_mem segs (arm W mem) (HA + 4) 4 0.
Proof.
  intros W mem HA [HZ _] k Hk.
  assert (L0 : forall w j, le_byte 0 w j = 0)
    by (intros w j; unfold le_byte; rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l;
        reflexivity).
  destruct (HZ (4 + k)%nat ltac:(rewrite repeat_length; unfold ASRC; cbn; lia)) as [H1 _].
  specialize (H1 0%nat ltac:(lia)). rewrite nth_repeat in H1.
  replace (HA + 4 + Z.of_nat k) with (HA + Z.of_nat (4 + k) + Z.of_nat 0) by lia.
  rewrite H1, !L0. reflexivity.
Qed.
(* op_add's afn_pre at sp = F: _latch.v's lt_afn_pre_at, from the saved registers alone (the prologue has not yet
   stored F+96 when it calls op_add) *)
(* _latch.v proves this with lia's default euclidean-division mode *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pro_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* a register op_add's post keeps *)
Ltac pro_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* values and arrays read through a kept view *)
Lemma pro_vm_view : forall (W W' : world segs) mem mem' a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HV Hv k Hk. specialize (Hv k Hk). unfold arm in *.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat k) (HV (a + Z.of_nat k) ltac:(lia))). exact Hv.
Qed.
Lemma pro_garr8_view : forall (W W' : world segs) mem mem' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  garr8 segs (arm W mem) a l -> garr8 segs (arm W' mem') a l.
Proof.
  intros W W' mem mem' a l HV Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (pro_vm_view W W' mem mem'); [|exact Hv]. intros x Hx. apply HV. lia.
Qed.
(* the fake frame keeps its place across a journal (frame_addr reads only ly_F, which layout_le keeps) *)
Lemma pro_ff_eq : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k cid pos,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
  reflexivity.
Qed.
(* the blocks after op_add, as ablocks_sep lists them *)
Lemma pro_sep_perm : forall (al al0 inp aob rest : list (Z * Z)) T T' q,
  Permutation al0 (inp ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aob ++ rest) ->
  ((T = 0 /\ Permutation al ((T', ATABLE) :: (q, APARTIAL) :: al0)) \/
   (T <> 0 /\ T' = T /\ Permutation al ((q, APARTIAL) :: al0))) ->
  Permutation al (inp ++ ((T', ATABLE) :: (q, APARTIAL) :: aob) ++ rest).
Proof.
  intros al al0 inp aob rest T T' q H0 [(HT & HP) | (HT & -> & HP)].
  - rewrite HT in H0. cbn [Z.eqb] in H0. rewrite HP, H0.
    exact (Permutation_app_swap_app [(T', ATABLE); (q, APARTIAL)] inp (aob ++ rest)).
  - rewrite (proj2 (Z.eqb_neq T 0) HT) in H0. rewrite HP, H0.
    eapply perm_trans; [exact (Permutation_app_swap_app [(q, APARTIAL)] inp ([(T, ATABLE)] ++ aob ++ rest))|].
    apply Permutation_app_head. apply perm_swap.
Qed.
(* a list without duplicates: an element of one part is not in the other, and a suffix has none *)
Lemma pro_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros l2 x HN H1 H2; [destruct H1|].
  inversion HN as [|a0 l0 Hna HN']; subst.
  destruct H1 as [<- | H1]; [apply Hna; apply in_or_app; right; exact H2 | exact (IH l2 x HN' H1 H2)].
Qed.
Lemma pro_nodup_app_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  induction l1 as [|a l1 IH]; cbn; intros l2 HN; [exact HN|]. inversion HN as [|a0 l0 _ HN']; subst. exact (IH l2 HN').
Qed.
(* a pairwise relation over two lists, across them *)
Lemma pro_pw_app : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; cbn; intros l2 x y Hp Hx Hy; [destruct Hx|].
  destruct Hp as [Hf Hp]. destruct Hx as [<- | Hx].
  - rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
  - exact (IH l2 x y Hp Hx Hy).
Qed.
(* a live block and a fake frame are apart (AR_sep_law) *)
Lemma pro_blk_frm : forall ly S (W : world segs) mem md p n cid pos, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  p + req_size n <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= p.
Proof.
  intros ly S W mem md p n cid pos HAR Hb Hf.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
  pose proof (pro_pw_app zdisjoint _ _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)) as H.
  unfold zdisjoint in H. cbn [fst snd] in H. exact H.
Qed.
(* the seven global stores of 0x841f8-0x8422c, as byte ranges *)
Definition pro_gst_out (a : Z) : Prop :=
  ~ (0xa1fe0 <= a < 0xa1fe4) /\ ~ (0x5d87e0 <= a < 0x5d87e1) /\ ~ (0x5d8820 <= a < 0x5d8824) /\
  ~ (0x5d8840 <= a < 0x5d8848) /\ ~ (0x5d8860 <= a < 0x5d8861) /\ ~ (0x5d8880 <= a < 0x5d8881) /\
  ~ (0x5d88a0 <= a < 0x5d88a1).
Definition pro_gstb (x : Z) : bool :=
  negb (((0xa1fe0 <=? x) && (x <? 0xa1fe4)) || ((0x5d87e0 <=? x) && (x <? 0x5d87e1)) ||
        ((0x5d8820 <=? x) && (x <? 0x5d8824)) || ((0x5d8840 <=? x) && (x <? 0x5d8848)) ||
        ((0x5d8860 <=? x) && (x <? 0x5d8861)) || ((0x5d8880 <=? x) && (x <? 0x5d8881)) ||
        ((0x5d88a0 <=? x) && (x <? 0x5d88a1))).
Lemma rng_bfalse : forall lo hi a, ((lo <=? a) && (a <? hi)) = false -> ~ (lo <= a < hi).
Proof. intros lo hi a H [H1 H2]. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in H. discriminate H. Qed.
Lemma pro_gstb_ok : forall a, pro_gstb a = true -> pro_gst_out a.
Proof.
  intros a H. unfold pro_gstb in H. apply negb_true_iff in H. rewrite !orb_false_iff in H.
  destruct H as ((((((H1 & H2) & H3) & H4) & H5) & H6) & H7).
  repeat split; apply rng_bfalse; assumption.
Qed.
Lemma G_keep_gst : forall a, inG G_keep a -> pro_gst_out a.
Proof. intros a Ha. apply pro_gstb_ok. exact (rng_all_in pro_gstb G_keep a ltac:(vm_compute; reflexivity) Ha). Qed.
Lemma pro_blk_gst : forall ly S (W : world segs) mem md p n a, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> pro_gst_out a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha. pose proof (blk_img segs B LAWS ly S W mem md p n a HAR Hin Ha) as Hni.
  assert (HI : forall lo w, rng_inb lo w G_fr_obj = true -> ~ (lo <= a < lo + w))
    by (intros lo w Hr Hx; apply Hni; exact (proj1 (HG a (HG_obj a (rng_cover lo w G_fr_obj Hr a Hx))))).
  split; [intros Hx; refine (HI 0xa1fe0 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d87e0 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8820 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8840 8 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8860 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8880 1 _ _); [vm_compute; reflexivity | lia]|].
  intros Hx; refine (HI 0x5d88a0 1 _ _); [vm_compute; reflexivity | lia].
Qed.
(* relay_add's globals, at fr_globals (W_op_add.v oa_ra_g) *)
Lemma pro_ra_g : forall a, inG (RA_G fr_globals) a ->
  0x5d8ac0 <= a < 0x5d8ac0 + 12 \/ 0x5d87a0 <= a < 0x5d87a0 + 4 \/ 0x5d8800 <= a < 0x5d8800 + 4 \/
  0x5d87c0 <= a < 0x5d87c0 + 8.
Proof.
  intros a Ha. unfold RA_G in Ha.
  apply inG_cons in Ha as [Ha | Ha]; [left; unfold in_zr, fr_globals, rg_lock in Ha; cbn [fst snd] in Ha; lia|].
  apply inG_cons in Ha as [Ha | Ha]; [right; left; unfold in_zr, fr_globals, rg_nsrc in Ha; cbn [fst snd] in Ha; lia|].
  apply inG_cons in Ha as [Ha | Ha];
    [right; right; left; unfold in_zr, fr_globals, rg_capsrc in Ha; cbn [fst snd] in Ha; lia|].
  apply inG_cons in Ha as [Ha | Ha];
    [right; right; right; unfold in_zr, fr_globals, rg_src in Ha; cbn [fst snd] in Ha; lia|].
  exfalso. exact (inG_nil a Ha).
Qed.
(* the prologue's global stores, as the call sees them *)
Definition pro_glob (W : world segs) (mem : word -> option byte) : Prop :=
  val_mem segs (arm W mem) (rg_client fr_RG) 4 3 /\ val_mem segs (arm W mem) (rg_client_broken fr_RG) 1 0 /\
  val_mem segs (arm W mem) A_NFD 4 0 /\ val_mem segs (arm W mem) (rg_send_max fr_RG) 8 0 /\
  val_mem segs (arm W mem) (rg_gone fr_RG) 1 0 /\ val_mem segs (arm W mem) (rg_send_dead fr_RG) 1 0 /\
  val_mem segs (arm W mem) (rg_send_eintr fr_RG) 1 0.
(* the bytes the prologue keeps from the entry to the call *)
Definition pro_ks (cx : lfcx) (a : Z) : Prop :=
  inG G_keep a \/ exists p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) /\ p <= a < p + req_size n.

(* ------------------------------------------------------------------ 0x84230 `jal op_add` *)
Lemma pro_mid : forall cx regs mem md S2 k fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) mem md k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  pro_fr cx (frame_addr (c_ly cx) 1 fpos) (c_W cx) mem ->
  sv8 (c_W cx) mem (frame_addr (c_ly cx) 1 fpos + 120) (flag_addr (c_ly cx) 1 fpos) ->
  getr regs 1 = w64 (BASE + A_pro_ret) -> pro_regs cx (frame_addr (c_ly cx) 1 fpos) regs ->
  pro_glob (c_W cx) mem ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) mem a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (cfg_at segs (BASE + AF_fr_op_add) regs mem md)
    (fun W' c' => INV_H B G_fr fr_FP LS RINV cx 0 W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx regs mem md S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HFR HFLG Hra HRG HGL KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hgi & Hrom & _).
  destruct Hgi as (HGP0 & HCL & (T & HRR) & (c0 & O & mx0 & cap & out & HAO) & (gn0 & HGN) & HLK & HWK & HTU &
    (lst & HLS0) & HLW).
  pose proof (pro_Fb cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof (HFP_pro cx T c0 O mx0 cap out HB HRR HAO) as ((rest0 & HPERM0) & HFPT & HFPO).
  set (W := c_W cx) in *. set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  assert (Hgs : rg_s fr_RG = 0x5d88e0) by (vm_compute; reflexivity).
  (* ---- kept from the entry to the call ---- *)
  assert (KG : forall a, inG G_keep a -> aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros a Ha; apply KEEP; left; exact Ha).
  assert (KBk : forall p n a, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> p <= a < p + req_size n ->
      aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros p0 n0 a Hp Ha; apply KEEP; right; exists p0, n0; split; [exact Hp | exact Ha]).
  assert (KGv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W mem) a n v).
  { intros a n0 v Hr Hv. apply (pro_vm_view W W (c_mem cx) mem); [|exact Hv].
    intros x Hx. exact (KG x (rng_cover a (Z.of_nat n0) G_keep Hr x Hx)). }
  assert (AW : forall a n, rng_inb a n G_fr_obj = true -> forall (W' : world segs) m', awr W' m' a n).
  { intros a n0 Hr W' m' i Hi. apply (G_obj_wr (a + i) (rng_cover a n0 G_fr_obj Hr (a + i) ltac:(lia))). }
  (* ---- the call's facts ---- *)
  assert (HCLc : forall i, (i < 4)%nat -> asrc_closed W mem (oa_HA i)).
  { intros i Hi. destruct (HCL i Hi) as [HZ _]. split.
    - apply (pro_garr8_view W W (c_mem cx) mem); [|exact HZ].
      intros x Hx. apply KG. rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply (rng_cover (rg_s fr_RG) 384 G_keep ltac:(vm_compute; reflexivity)).
      unfold oa_HA, fr_RG in *. unfold ASRC in Hx. rewrite Hgs in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->|[->| ->]]]; vm_compute; reflexivity. }
  assert (Hos : forall i, nth i [0; 0; 0; 0] 0 = 0) by (intros i; destruct i as [|[|[|[|[|i]]]]]; reflexivity).
  assert (HRRc : ra_rel B fr_RG (c_ly cx) S2 W mem T []).
  { destruct HRR as [(HT0 & _ & (E1 & E2 & E3 & E4 & E5 & E6)) | HAT].
    - left. split; [exact HT0|]. split; [reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E1]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E3]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E5] | apply AW; vm_compute; reflexivity].
    - right. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
      apply (arelay_at_kept B fr_RG (c_ly cx) (c_S cx) W (c_mem cx) (c_ly cx) S2 W mem T [] HAT).
      + intros r Hr a Ha. split.
        * unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- apply KG. refine (rng_cover (rg_src fr_RG) 8 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_nsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_capsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply (KBk T ATABLE a HTin). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
        * intros _. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- refine (G_obj_wr a (rng_cover (rg_src fr_RG) 8 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- rewrite <- Eab2 in HTin.
             destruct (al_blocks _ _ LAWS _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & _ & Hpr & _).
             apply (apresent_writable segs). apply (proj1 (Hpr a ltac:(change (req_size ATABLE) with 896;
               unfold ATABLE in Ha; lia))).
      + intros b Hb. rewrite Eab2. cbn [arelay_blks map concat app] in Hb. destruct Hb as [<- | []]. exact HTin. }
  assert (HLKc : alock_at fr_RG W mem false).
  { destruct HLK as (L1 & L2 & L3 & L4).
    split; [apply KGv; [vm_compute; reflexivity | exact L1]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L2]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L3] | apply AW; vm_compute; reflexivity]. }
  assert (HWKc : awake_at fr_RG W mem) by (apply KGv; [vm_compute; reflexivity | exact HWK]).
  assert (HRVc : rom_view segs W mem)
    by (eapply ajournal_gx_rom_view; first [exact Hsegs | exact LAWS | exact HJ | exact pro_rom_out_fr | exact Hrom]).
  (* ---- op_add's afn_pre, its room and its meter ---- *)
  pose proof HFR as (HSV & H24 & H48 & H56 & H64 & H72 & H80 & H88 & H184 & HH0 & HH8 & HH16 & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R21 & R22 & R24 & R26 & R3 & R4).
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  destruct (pro_afn_pre_at cx (c_ly cx) S2 fpos k W mem md regs OA_STK HB HJ HSV Hsp) as (ch & HPREc).
  { rewrite Hra. apply ret_ok_codeptr_v; [unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite Hra, unsigned_lit_small by (unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia).
    unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput. lia. }
  { exact R3. } { exact R4. } { exact R8. }
  { unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK. lia. }
  { unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK, LLVMF_STK. lia. }
  destruct (LS_pro_oa cx S2 fpos HB Eab2 Hfrs2 Hnev2 Hbb2) as (Hroom & Hmok).
  (* the entry's T: when the table exists it is a live block of the entry, above 4096 *)
  assert (HT4096 : T <> 0 -> 4096 <= T /\ In (T, ATABLE) (ablocks B (c_ly cx) (c_S cx))).
  { intros HT0. destruct HRR as [(HT0' & _) | HAT]; [contradiction|].
    pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _). split; [|exact HTin]. rewrite <- Eab2 in HTin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & H4096 & _). exact H4096. }
  (* ---- op_add, at its own G ---- *)
  assert (HGcov1 : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G_oa a).
  { intros a Ha. change (inG ((rg_s fr_globals, 384) :: (A_NFD, 4) :: RA_G fr_globals) a).
    apply inG_cons. left. unfold in_zr, ASRC in *. cbn [fst snd]. lia. }
  assert (HGcov2 : forall a, A_NFD <= a < A_NFD + 4 -> inG G_oa a).
  { intros a Ha. change (inG ((rg_s fr_globals, 384) :: (A_NFD, 4) :: RA_G fr_globals) a).
    apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
  assert (HGcov3 : forall a, inG (RA_G fr_globals) a -> inG G_oa a)
    by (intros a Ha; unfold G_oa; apply inG_app; right; exact Ha).
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply SRr_bind.
  { exact (W2_op_add G_oa G_oa_prog W (c_ly cx) S2 regs mem md ch [0; 0; 0; 0] 0 T [] HPREc
      ltac:(rewrite Hsp; exact HFal) ltac:(rewrite Hfrs2; vm_compute; reflexivity) eq_refl
      ltac:(intros i _; rewrite Hos; lia)
      ltac:(intros i Hi; rewrite Hos; exact (pro_closed_vm W mem _ (HCLc i Hi)))
      ltac:(intros i Hi _; exact (HCLc i Hi))
      G3 ltac:(lia) HZS HGcov1 HGcov2 HGcov3 HRRc HLKc HWKc HRVc
      ltac:(intros _; split; [cbn; lia | intros []]) Hroom Hmok). }
  cbv beta. intros W3 c3 Hwle3 (ly4 & S4 & regs4 & mem4 & md4 & kk & -> & HJo & HP4 & HAPK & HOK & Hfrs4 & HSome & HERR4).
  assert (Hof : oa_first [0; 0; 0; 0] = Some 0%nat) by reflexivity.
  rewrite Hof in HSome. cbv beta iota in HSome.
  destruct HSome as (q & T' & pj & HSRC & HNFD & HREL & HLK4 & HPERM & HMLE).
  cbn [app] in HREL. change (100 + 0) with 100 in HSRC, HREL. change (0 + 1) with 1 in HNFD.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo) as HAR4.
  assert (Hsk : ~ YI16.sink_open_fp (oa_FP [0; 0; 0; 0] T [])).
  { unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
    intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & _). lia. }
  (* the journal from the entry, through op_add (lifted from G_oa to G_fr) *)
  pose proof (ajournal_gx_G_mono segs B G_oa G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_oa_fr HJo) as HJo'.
  assert (HFP1 : forall a, inFP (oa_FP [0; 0; 0; 0] T []) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B (c_ly cx) S2) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B (c_ly cx) S2) a).
  { intros a Ha. left. unfold oa_FP in Ha. rewrite Hof in Ha. unfold ra_FP in Ha.
    destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Ha as (r & [] & _)|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & HTin).
    split; [apply (HFPT HT0); change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
    exists T, ATABLE. split; [rewrite Eab2; exact HTin | change (req_size ATABLE) with 896; lia]. }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 W mem md k
     OA_STK (spZ regs) 0 [] (oa_FP [0; 0; 0; 0] T []) [] ly4 S4 W3 mem4 md4 kk HJ HJo'
     ltac:(rewrite Hsp; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK, LLVMF_STK; lia)
     ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ4.
  cbn [app] in HJ4.
  assert (EFF : frame_addr ly4 1 fpos = FF) by exact (pro_ff_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJo).
  assert (EFL : flag_addr ly4 1 fpos = flag_addr (c_ly cx) 1 fpos)
    by (pose proof EFF as E'; unfold FF, frame_addr in E'; unfold flag_addr; lia).
  (* ---- what op_add keeps ---- *)
  assert (KP : forall a, inG G_pst a -> aview segs (w_H W3) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. pose proof (G_pst_obj a Ha) as Ho. destruct (HG a (HG_obj a Ho)) as (Him & Hno & _).
    exact (pro_call_img G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo Hsk a Him (G_pst_oa a Ha) Hno
      (G_obj_err a Ho)). }
  assert (KPv : forall a n v, rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W3 mem4) a n v).
  { intros a n0 v Hr Hv. apply (pro_vm_view W W3 mem mem4); [|exact Hv].
    intros x Hx. exact (KP x (rng_cover a (Z.of_nat n0) G_pst Hr x Hx)). }
  assert (KGPv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true -> rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W3 mem4) a n v)
    by (intros a n0 v H1 H2 Hv; exact (KPv a n0 v H2 (KGv a n0 v H1 Hv))).
  assert (Hgs' : rg_s fr_globals = 0x5d88e0) by (vm_compute; reflexivity).
  assert (KS3 : forall i, (1 <= i < 4)%nat -> asrc_closed W3 mem4 (oa_HA i)).
  { intros i Hi. destruct (HCLc i ltac:(lia)) as [HZ _]. split.
    - apply (pro_garr8_view W W3 mem mem4); [|exact HZ]. intros x Hx.
      rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply HOK.
      + apply HGcov1. unfold oa_HA, ASRC in *. rewrite Hgs' in *. lia.
      + unfold oa_wr. rewrite Hof. intros [Hx1 | [Hx2 | Hx3]].
        * unfold oa_HA, ASRC in *. cbn [Z.of_nat] in Hx1. rewrite Hgs' in *. lia.
        * unfold oa_HA, ASRC, A_NFD in *. rewrite Hgs' in *. lia.
        * pose proof (pro_ra_g x Hx3). unfold oa_HA, ASRC in *. rewrite Hgs' in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->| ->]]; vm_compute; reflexivity. }
  (* the entry's blocks the call keeps: all but the relay's table, whose new entry relay_add writes *)
  assert (KBo : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) mem (p + j)).
  { intros p n j Hp Hne Hj. assert (Hp2 : In (p, n) (ablocks B (c_ly cx) S2)) by (rewrite Eab2; exact Hp).
    apply (pro_call_blk G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk (proj1 G_oa_prog) HJo p n j Hp2).
    - destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)).
      + right. right. exact Hp2.
      + right. exact Hp2.
    - exact Hj.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (pro_blk_disj _ _ _ _ _ (p, n) (T, ATABLE) HAR2 Hp2 HTin (Hne HT0)) as [Hd | Hd]; cbn [fst snd] in Hd;
        change (req_size ATABLE) with 896 in Hd; lia. }
  (* the input block and the controller's buffer are not the relay's table (the entry's blocks are distinct) *)
  assert (ND0 : List.NoDup (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest0)).
  { pose proof HPREE as (HAR0 & _). exact (Permutation_NoDup HPERM0 (pro_nodup _ _ _ _ _ HAR0)). }
  assert (HinpT : forall p n, In (p, n) (input_blks cx) -> T <> 0 -> (p, n) <> (T, ATABLE)).
  { intros p n Hp HT0 Heq. rewrite Heq in Hp. apply (pro_nodup_app _ _ (T, ATABLE) ND0 Hp).
    rewrite (proj2 (Z.eqb_neq T 0) HT0). apply in_or_app. left. left. reflexivity. }
  assert (HoutT : forall b, In b (aout_blks cap out) -> T <> 0 -> b <> (T, ATABLE)).
  { intros b Hb HT0 Heq. rewrite Heq in Hb. pose proof (pro_nodup_app_r _ _ ND0) as ND1.
    rewrite (proj2 (Z.eqb_neq T 0) HT0) in ND1. cbn [app] in ND1. inversion ND1 as [|x l Hx _]; subst.
    apply Hx. apply in_or_app. left. exact Hb. }
  assert (KBt : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) (c_mem cx) (p + j))
    by (intros p n j Hp Hne Hj; rewrite (KBo p n j Hp Hne Hj); exact (KBk p n (p + j) Hp ltac:(lia))).
  (* ---- the cut after op_add: the controller's stream ---- *)
  destruct (ERRL ly4 S4 W3 mem4 md4 HAR4) as ((v & Hv & Hvr) & Hvw).
  pose proof HAO as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26).
  assert (HAOp : aout_at B fr_RG ly4 S4 W3 mem4 (W_rep.CTL 3 0 0 0 v) O 0 (Z.of_nat (length O)) cap out).
  { split; [apply KPv; [vm_compute; reflexivity | exact G4]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A3]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A5]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A7]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G1]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G2]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G6]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G7]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [exact Hv|]. split; [exact Hvw|]. split; [exact Hvr|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    destruct A26 as [A26 | (Hc & Hnc & Hio & junk & Hjl & Hjg)]; [left; exact A26|].
    right. split; [exact Hc|]. split; [exact Hnc|].
    assert (Hio2 : In (out, cap) (ablocks B ly4 S4)).
    { destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hio. }
    split; [exact Hio2|]. exists junk. split; [exact Hjl|].
    apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hjg].
    intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx.
    replace x with (out + (x - out)) by lia.
    apply (KBt out cap (x - out)); [exact Hio | intros HT0; apply (HoutT (out, cap));
      [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)); left; reflexivity | exact HT0] |].
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hrc]. lia. }
  (* the input *)
  assert (HINp : ainput_at B cx ly4 S4 W3 mem4).
  { split.
    - destruct Hin as [Hin | (Hn & Hpin)]; [left; exact Hin|]. right. split; [exact Hn|].
      destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hpin.
    - destruct Hin as [(Hn0 & _) | (Hn & Hpin)].
      + rewrite Hnl in Hn0. assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hpl. intros j Hj. cbn in Hj. lia.
      + apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hgarr].
        intros x Hx. rewrite length_map in Hx. rewrite <- Hnl in Hx. replace x with (c_p cx + (x - c_p cx)) by lia.
        apply (KBt (c_p cx) (c_n cx) (x - c_p cx)); [exact Hpin | intros HT0; apply (HinpT (c_p cx) (c_n cx));
          [unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity | exact HT0] |].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrc]. lia. }
  (* the model *)
  assert (HMOD4 : amodel_at B ly4 S4 W3 mem4 (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out)).
  { unfold amodel_at, pro_m. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [reflexivity|].
    split.
    { intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth aslot].
      - exact HSRC.
      - exact (KS3 1%nat ltac:(lia)).
      - exact (KS3 2%nat ltac:(lia)).
      - exact (KS3 3%nat ltac:(lia)).
      - lia. }
    split; [exact HREL|]. split; [exact HAOp|].
    split; [split; [apply KPv; [vm_compute; reflexivity | exact G5]
                  | split; [apply AW; vm_compute; reflexivity | left; reflexivity]]|].
    split; [exact HLK4|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HWK]|].
    split; [exact HNFD|]. split; [apply AW; vm_compute; reflexivity|]. split; [unfold OPS_MAX; lia|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HTU]|].
    split; [exists lst; apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HLS0]|].
    apply AW; vm_compute; reflexivity. }
  (* the frame and the fake frame *)
  assert (HIV : forall x, F <= x < 2 ^ 47 -> aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_call_hi G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk (proj1 G_oa_prog) HJo x).
    - unfold CEIL8 in *. lia.
    - rewrite Hsp. lia. }
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HAR2 Hin1) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FRV : forall x, (FF <= x < FF + 128) \/ (SB + FF / 8 <= x < SB + FF / 8 + 16) ->
      aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_call_frm G_oa OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo 1 fpos x Hin1).
    - unfold frame_rng, in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. fold FF. lia.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & Happ & _).
      change (req_size ATABLE) with 896 in Happ.
      destruct Hx as [Hx | Hx].
      + destruct (pro_blk_frm _ _ _ _ _ T ATABLE 1 fpos HAR2 HTin Hin1) as [Hd | Hd];
          change (req_size ATABLE) with 896 in Hd; change (fs_frame_bytes 1) with 128 in Hd; fold FF in Hd; lia.
      + apply (fshadow_not_app FF 16 T 896 x ltac:(lia) ltac:(lia) Happ); [unfold SB in Hx; lia | lia].
    - unfold SB in *. lia.
    - intros HO. pose proof (G_obj_rng x (G_oa_obj x HO)). unfold SB in *. lia. }
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4, Hfrs2; left; reflexivity).
  destruct (al_frames _ _ LAWS ly4 S4 W3 mem4 md4 1 fpos HAR4 Hin4) as (_ & _ & HFp & HFs).
  rewrite EFF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFR4 : pro_fr cx FF W3 mem4).
  { split.
    { intros o r Hor. apply (pro_vm_view W W3 mem mem4); [|exact (HSV o r Hor)].
      intros x Hx. apply HIV. unfold saved_regs in Hor. cbn [In] in Hor.
      repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; unfold sp0 in *; lia|]). destruct Hor. }
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H24]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H48]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H56]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H64]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H72]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H80]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H88]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H184]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH0]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH8]|].
    split; [apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH16]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split; [apply (pro_garr8_view W W3 mem mem4); [intros x Hx; apply FRV; right; cbn [length fake_shadow] in Hx; lia
            | exact HSH]|].
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the fake frame's last word, its flag pointer (op_add keeps the fake frame) *)
  assert (HFL4 : sv8 W3 mem4 (FF + 120) (flag_addr (c_ly cx) 1 fpos))
    by (apply (pro_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HFLG]).
  (* the registers op_add keeps *)
  assert (HRG4 : pro_regs cx FF regs4).
  { split; [rewrite (lt_pres regs regs4 2%bv HP4 ltac:(pro_cs)); exact R2|].
    split; [rewrite (lt_pres regs regs4 8%bv HP4 ltac:(pro_cs)); exact R8|].
    split; [rewrite (lt_pres regs regs4 9%bv HP4 ltac:(pro_cs)); exact R9|].
    split; [rewrite (lt_pres regs regs4 21%bv HP4 ltac:(pro_cs)); exact R21|].
    split; [rewrite (lt_pres regs regs4 22%bv HP4 ltac:(pro_cs)); exact R22|].
    split; [rewrite (lt_pres regs regs4 24%bv HP4 ltac:(pro_cs)); exact R24|].
    split; [rewrite (lt_pres regs regs4 26%bv HP4 ltac:(pro_cs)); exact R26|].
    split; [rewrite (lt_pres regs regs4 3%bv HP4 ltac:(pro_cs)); exact R3|].
    rewrite (lt_pres regs regs4 4%bv HP4 ltac:(pro_cs)); exact R4. }
  (* the blocks, as ablocks_sep lists them *)
  assert (Em : model_blks (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (ND4 : List.NoDup (ablocks B ly4 S4)) by exact (pro_nodup _ _ _ _ _ HAR4).
  assert (HSEP4 : ablocks_sep B fr_FP cx (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) ly4 S4).
  { split.
    - exists rest0. rewrite Em. rewrite Eab2 in HPERM. exact (pro_sep_perm _ _ _ _ _ T T' q HPERM0 HPERM).
    - intros b Hb. rewrite Em in Hb. destruct Hb as [<- | [<- | Hb]].
      + destruct HPERM as [(HT0 & HP) | (HT0 & -> & HP)].
        * left. intros Hb'. pose proof (Permutation_NoDup HP ND4) as ND. inversion ND as [|x l Hx ND']; subst.
          apply Hx. right. rewrite Eab2. exact Hb'.
        * right. intros a Ha. cbn [fst snd] in Ha. exact (HFPT HT0 a Ha).
      + left. intros Hb'. destruct HPERM as [(_ & HP) | (_ & _ & HP)]; pose proof (Permutation_NoDup HP ND4) as ND.
        * inversion ND as [|x l _ ND']; subst. inversion ND' as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
        * inversion ND as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
      + right. exact (HFPO b Hb). }
  (* the cut's two Variables, and the ROM view after op_add *)
  assert (Hc0ex : exists c1 mx1, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c1 O mx1
    (Z.of_nat (length O)) cap out) by (exists c0, mx0; exact HAO).
  assert (HPERM' : exists T0 rest, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest) /\
     ((T0 = 0 /\ Permutation (ablocks B ly4 S4) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly4 S4) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))))
    by (exists T, rest0; split; [exact HPERM0 | rewrite <- Eab2; exact HPERM]).
  pose proof (LS_pro cx q T' pj (W_rep.CTL 3 0 0 0 v) O cap out S2 fpos ly4 S4 HB Hc0ex eq_refl eq_refl eq_refl
    eq_refl Eab2 Hfrs2 Hnev2 Hbb2 HMLE HPERM') as HLS4.
  pose proof (RI_pro cx q T' pj (W_rep.CTL 3 0 0 0 v) O cap out HB Hc0ex eq_refl eq_refl eq_refl eq_refl) as HRI4.
  assert (HRV4 : rom_view segs W3 mem4)
    by (eapply ajournal_gx_rom_view;
        first [exact Hsegs | exact LAWS | exact HJo | exact (proj1 (proj2 (proj2 G_oa_prog))) | exact HRVc]).
  (* the loop's set-up *)
  rewrite Hra. rewrite <- EFF in HFR4, HRG4, HFL4. rewrite <- EFL in HFL4.
  exact (pro_fin cx W3 regs4 mem4 md4 ly4 S4 (k + kk) _ fpos HB HJ4 HFR4 HRG4 HFL4 HMOD4 eq_refl HINp HRV4 HSEP4 HLS4 HRI4).
Qed.
(* ------------------------------------------------------------------ the state at op_add's entry (0x84f10) *)
(* the regions of the token run's state when it reaches op_add (as the run leaves them) *)
Definition pc_g (n : nat) (off w : Z) (sz : N) (v : Z) : YP09.region :=
  YP09.mkRegion (Some n) off (off + w) off (off + w) [YP09.mkChunk off (CVal sz (SLit v))].
Definition pc_sh : YP09.region := YP09.mkRegion (Some 513%nat) 0 16 0 0
  [YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601))].
Definition pc_ff : YP09.region := YP09.mkRegion (Some 39%nat) 0 128 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 240 7620)); YP09.mkChunk 8 (CVal 8 (SOff 266 0));
   YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 120 (CVal 8 (SOff 512 0))].
Definition pc_save : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition pc_F : YP09.region := YP09.mkRegion (Some 34%nat) 24 208 24 208
  [YP09.mkChunk 56 (CVal 8 (SOff 353 0)); YP09.mkChunk 48 (CVal 8 (SOff 352 0));
   YP09.mkChunk 64 (CVal 8 (SOff 351 0)); YP09.mkChunk 72 (CVal 8 (SOff 350 0));
   YP09.mkChunk 24 (CVal 8 (SOff 347 0)); YP09.mkChunk 80 (CVal 8 (SOff 39 0));
   YP09.mkChunk 88 (CVal 8 (SOff 39 0)); YP09.mkChunk 184 (CVal 8 (SOff 39 0))].
Lemma vm_at : forall m a a' (n n' : nat) v, val_mem segs m a n v -> a = a' -> n = n' -> val_mem segs m a' n' v.
Proof. intros m a a' n n' v H -> ->. exact H. Qed.
(* an image atom's value, by computation *)
Ltac pro_rwimg HEI n :=
  let v := eval vm_compute in (VAL n) in
  rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia));
  replace (VAL n) with v by (vm_compute; reflexivity).
Lemma pro_at_call : forall cx S2 k fpos E regs4 m4 md4,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) m4 md4 k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) -> bv_unsigned (ew E 34) = lf_F cx ->
  bv_unsigned (ew E 39) = frame_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 513) = SB + frame_addr (c_ly cx) 1 fpos / 8 -> ew E 33 = Z_to_bv 64 SB ->
  bv_unsigned (ew E 512) = flag_addr (c_ly cx) 1 fpos ->
  (forall r, (r < 32)%nat -> ew E r = getr (c_regs cx) (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 353 1684 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 352 1660 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 351 1636 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 350 1616 8 8 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 349 1588 4 4 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 348 1528 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 347 (-512) 4 4 3) ->
  region_ok segs E (arm (c_W cx) m4) pc_sh -> region_ok segs E (arm (c_W cx) m4) pc_ff ->
  region_ok segs E (arm (c_W cx) m4) pc_save -> region_ok segs E (arm (c_W cx) m4) pc_F ->
  getr regs4 1 = Z_to_bv 64 (BASE + 8008) -> getr regs4 2 = ew E 34 -> getr regs4 3 = ew E 3 ->
  getr regs4 4 = ew E 4 -> getr regs4 8 = ew E 2 -> getr regs4 9 = ew E 34 -> getr regs4 21 = ew E 11 ->
  getr regs4 22 = ew E 10 -> getr regs4 24 = ew E 513 -> getr regs4 26 = ew E 33 ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) m4 a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 11300)) m4 (seg_rom segs)) md4)
    (fun W' c' => INV_H B G_fr fr_FP LS RINV cx 0 W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros cx S2 k fpos E regs4 m4 md4 HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HEI U2 U34 U39 U513 E33 U512 EA
    RG7 RG6 RG5 RG4 RG3 RG2 RG1 RSH RFF RSV RF Q1 Q2 Q3 Q4 Q8 Q9 Q21 Q22 Q24 Q26 KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & _).
  pose proof HPREE as (_ & _ & _ & Hgp & Htp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (pro_Fb cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & HFp & HFs).
  fold FF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (ER : forall (r : nat) (b : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned b -> ew E r = getr (c_regs cx) b).
  { intros r b Hr Hb. rewrite (EA r Hr). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb.
    apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  (* the frame and the fake frame *)
  assert (HFR : pro_fr cx FF (c_W cx) m4).
  { unfold pro_fr. cbv zeta. fold F.
    split.
    { apply (pro_saved_of_region E _ _ _ _ _ _ _ (c_regs cx) RSV U2 EA).
      unfold saved_regs.
      repeat (apply Forall_cons; [cbn [fst snd In]; repeat (first [left; reflexivity | right]) |]).
      apply Forall_nil. }
    assert (FS : forall off (nv : nat) v, In (YP09.mkChunk off (CVal 8 (SOff nv 0))) (YP09.r_chunks pc_F) ->
        bv_unsigned (ew E nv) = v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (F + off) v).
    { intros off nv v Hc Hv Hr. unfold sv8.
      refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 34 F _ 24 208 24 208 off 8 (SOff nv 0) v RF U34 Hc _ Hr
        ltac:(cbn; lia)) eq_refl eq_refl).
      cbn [sv_denot]. rewrite Hv, Z.add_0_r. reflexivity. }
    split; [apply (FS 24 347%nat); [cbn; tauto | pro_rwimg HEI 347%nat; reflexivity | lia]|].
    split; [apply (FS 48 352%nat); [cbn; tauto | pro_rwimg HEI 352%nat; reflexivity | lia]|].
    split; [apply (FS 56 353%nat); [cbn; tauto | pro_rwimg HEI 353%nat; reflexivity | lia]|].
    split; [apply (FS 64 351%nat); [cbn; tauto | pro_rwimg HEI 351%nat; reflexivity | lia]|].
    split; [apply (FS 72 350%nat); [cbn; tauto | pro_rwimg HEI 350%nat; reflexivity | lia]|].
    split; [apply (FS 80 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 88 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 184 39%nat); [cbn; tauto | exact U39 | lia]|].
    assert (FH : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks pc_ff) ->
        sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (FF + off) v).
    { intros off e v Hc Hv Hr. unfold sv8.
      exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 off 8 e v RFF U39 Hc Hv Hr
        ltac:(cbn; lia)) eq_refl eq_refl). }
    split; [rewrite <- (Z.add_0_r FF); apply (FH 0 (SLit 1102416563)); [cbn; tauto | reflexivity | lia]|].
    split; [apply (FH 8 (SOff 266 0)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 266%nat; reflexivity|].
    split; [apply (FH 16 (SOff 240 7620)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 240%nat; reflexivity|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split.
    { apply (pro_shadow_garr8 E _ 513 _ _ 0 16 0 0 RSH U513).
      intros j Hj. do 16 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]). lia. }
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers *)
  assert (HRG : pro_regs cx FF regs4).
  { unfold pro_regs, w64. fold F.
    split; [rewrite Q2, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q8, (ER 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
    split; [rewrite Q9, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q21, (ER 11%nat 11%bv ltac:(lia) eq_refl), H11; reflexivity|].
    split; [rewrite Q22, (ER 10%nat 10%bv ltac:(lia) eq_refl), H10; reflexivity|].
    split; [rewrite Q24, <- U513, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q26; exact E33|].
    split; [rewrite Q3, (ER 3%nat 3%bv ltac:(lia) eq_refl), Hgp; reflexivity|].
    rewrite Q4, (ER 4%nat 4%bv ltac:(lia) eq_refl), Htp; reflexivity. }
  (* the globals *)
  assert (GV : forall n off w (sz : N) v a, region_ok segs E (arm (c_W cx) m4) (pc_g n off w sz v) ->
      (A_TEXT <= n < A_LIM)%nat -> VAL n + off = a -> N.to_nat sz = Z.to_nat w -> 0 <= v < 2 ^ (8 * Z.of_N sz) ->
      (Z.of_N sz <= 8) -> val_mem segs (arm (c_W cx) m4) a (Z.to_nat w) v).
  { intros n0 off w sz v a HR Hn Ha Hw Hv Hs.
    refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ n0 (VAL n0) _ off (off + w) off (off + w) off sz
      (SLit v) v HR (HEI n0 Hn) ltac:(cbn; tauto) _ Hv Hs) Ha Hw).
    reflexivity. }
  assert (HGL : pro_glob (c_W cx) m4).
  { unfold pro_glob.
    split; [exact (GV 347%nat (-512) 4 4%N 3 (rg_client fr_RG) RG1 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 348%nat 1528 1 1%N 0 (rg_client_broken fr_RG) RG2 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 349%nat 1588 4 4%N 0 A_NFD RG3 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 350%nat 1616 8 8%N 0 (rg_send_max fr_RG) RG4 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 351%nat 1636 1 1%N 0 (rg_gone fr_RG) RG5 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 352%nat 1660 1 1%N 0 (rg_send_dead fr_RG) RG6 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    exact (GV 353%nat 1684 1 1%N 0 (rg_send_eintr fr_RG) RG7 ltac:(unfold A_TEXT, A_LIM; lia)
      ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the return address *)
  assert (Hra : getr regs4 1 = w64 (BASE + A_pro_ret)).
  { rewrite Q1. reflexivity. }
  assert (HFLG : sv8 (c_W cx) m4 (FF + 120) (flag_addr (c_ly cx) 1 fpos)).
  { pose proof (bv_unsigned_in_range 64 (ew E 512)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    unfold sv8.
    exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 120 8 (SOff 512 0)
      (flag_addr (c_ly cx) 1 fpos) RFF U39 ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite U512, Z.add_0_r; reflexivity) ltac:(rewrite <- U512; lia)
      ltac:(cbn; lia)) eq_refl eq_refl). }
  exact (pro_mid cx regs4 m4 md4 S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HFR HFLG Hra HRG HGL KEEP).
Qed.
(* ------------------------------------------------------------------ the walk *)
(* ~ in_wrange E rs a, region by region: each window is read off (its base by the U facts in context, an image base by
   HEIx) and refuted by a lia over few facts: an empty window; a stack window above F (Ha, HFlo, HFsp); a window the
   one fact Hk about a misses *)
Ltac pro_nwr_k HEIx Ha HFlo HFsp :=
  let r := fresh "r" in let Hin' := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin' & Hr);
  lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end;
  cbn [In] in Hin';
  repeat (destruct Hin' as [<- | Hin'];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      repeat match goal with Hu : bv_unsigned (ew ?E ?x) = _ |- _ =>
        match type of Hr with context [bv_unsigned (ew E x)] => rewrite Hu in Hr end end;
      pro_imgh HEIx Hr; unfold SB in Hr;
      first [ clear - Hr; lia
            | clear - Hr Ha HFlo HFsp; lia
            | match goal with Hk : ~ (_ <= _ < _) |- _ => clear - Hr Hk; lia end
            | match goal with Hk : (_ \/ _) |- _ => clear - Hr Hk; lia end ] | ]);
  destruct Hin'.
Theorem lf_seg_pro : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  SRr segs (c_W cx) (lf_entry cx)
    (fun W' c' => INV_H B G_fr fr_FP LS RINV cx 0 W' c' \/ INV_X B G_fr fr_FP LS RINV cx W' c').
Proof.
  intros [ly S W regs mem md p n pl M] HB.
  pose proof HB as (HAI & HPRE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hgi & Hrom & Hrod & Hsink & Hfd & Hsrt & Hmeta & Hmo & Hstkr & Hhb).
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M lf_entry] in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  assert (Rn : 0 <= n < 2 ^ 26) by (destruct Hin as [(-> & _) | (Hn & _)]; lia).
  destruct (pro_entry W ly S regs mem md [] n HPRE H11 Rn) as [HS SHOK].
  pose proof (ajournal_init segs B LLVMF_STK (lf_FP fr_FP (LFCX ly S W regs mem md p n pl M)) ly S W regs mem md [] HPRE) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  remember (Eimg (Ereg regs (pro_extra regs))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  set (F := pro_F regs) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (pro_extra regs)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 (BASE + A_pro)).
  (* run 1: the frame, the saved registers, the fake-stack test; stops at __asan_stack_malloc_1 *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UF in Hr;
        first [ lia | left; lia ] | ]).
    destruct Hin'. }
  (* the call to __asan_stack_malloc_1 (128): the fake frame FF *)
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite (palf_sm1 B TLF).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
      eapply (aj_stack_malloc_pres_at segs B LAWS Hsegs (pal_env B TL) ML SMP 1 ASM1 ltac:(lia) W rg mm LLVMF_STK (spZ regs)
        _ ly S W mem md [] ly S _ 0 (F - spZ regs) _ HJ) end.
    - unfold spZ at 1. rewrite R2, UF. lia.
    - destruct HFv as [HFe | HFe]; rewrite HFe;
        [replace (spZ regs - 320 - spZ regs) with ((-20) * 16) by lia | replace (spZ regs - 336 - spZ regs) with ((-21) * 16) by lia];
        apply Z_mod_mult.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfrs. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPg).
  set (FF := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
  pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
  destruct (al_const _ _ LAWS _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
  destruct (al_const _ _ LAWS _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
  rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
  pose proof (palf_uar_img B TLF) as HuR.
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
    - eapply (region_kept_stack_aj segs B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply (region_kept_stack_aj segs B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply (region_kept_stack_aj segs B); [exact HK | exact HJ2 | exact UF | lia | lia | lia | cbn; lia | cbn; lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
        [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kg1) | exact (val_mem_of_rdword segs _ _ _ _ Kg2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
        [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kc1) | exact (val_mem_of_rdword segs _ _ _ _ Kc2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
        [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kgu1) | exact (val_mem_of_rdword segs _ _ _ _ Kgu2) | lia].
    - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
        [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 segs _ _ _ _ Ku1) | exact (val_mem_of_rd32 segs _ _ _ _ Ku2) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEa : env_agree 32 (Ereg regs (pro_extra regs)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  clear HEa.
  prreg HS (10%bv : bv 5) RF.
  (* seat the fake frame: FF in atom 39 (a0), its flag FL in 512, the frame's shadow SB + FF / 8 in 513 *)
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal2 & HFapp & HFpres & HFSpres).
  destruct (FFL _ _ _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  fold FF FL in HFal2, HFapp, HFpres, HFSpres, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
  assert (RF' : ew Ea 39 = Z_to_bv 64 FF) by (rewrite <- RF, Ha0; reflexivity).
  assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
  assert (U2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
  assert (U34a : bv_unsigned (ew Ea 34) = F) by (rewrite OLDa by lia; exact UF).
  assert (U32a : bv_unsigned (ew Ea 32) = as_uar_cell B) by (rewrite OLDa, E32 by lia; apply unsigned_lit_small; lia).
  assert (U241 : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)) by exact (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U242 : bv_unsigned (ew Ea 242) = VAL (A_OBJ 1)) by exact (HEIa (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U273 : bv_unsigned (ew Ea 273) = VAL (A_OBJ 32)) by exact (HEIa (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (HFF8 : FF / 8 = 4 * (FF / 32)).
  { pose proof (Z.div_mod FF 32 ltac:(lia)) as D. rewrite HFal2, Z.add_0_r in D. rewrite D at 1.
    replace (32 * (FF / 32)) with (4 * (FF / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (HFF8lo : 512 <= FF / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HFF8hi : FF / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
  pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
  pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 1)). pose proof (pa_val_range (A_OBJ 32)).
  pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 39 33 512 1 FF FL HS eq_refl ltac:(vm_compute; reflexivity)
    RF' E33a ltac:(lia) ltac:(lia) ltac:(right; reflexivity) HFal2 ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia)
    ltac:(lia)
    ltac:(change (fs_frame_bytes 1) with 128; intros a Ha; exact (proj1 (HFpres a Ha)))
    ltac:(change (fs_frame_bytes 1 / 8) with 16; intros i Hi; exact (proj1 (HFSpres i Hi)))
    ltac:(change (fs_frame_bytes 1) with 128; exact Hflag) ltac:(change (fs_frame_bytes 1) with 128; exact Hz)) as HS3.
  pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HARb Hfin2) as HFimg. change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg.
  set (Eb := havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)]) in HS3.
  assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; subst Eb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
  assert (U512 : bv_unsigned (ew Eb 512) = FL).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. lia. }
  assert (U513 : bv_unsigned (ew Eb 513) = SB + FF / 8).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. unfold SB. lia. }
  assert (U39b : bv_unsigned (ew Eb 39) = FF) by (rewrite OLDb, RF' by lia; apply unsigned_lit_small; lia).
  assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact U2a).
  assert (U34b : bv_unsigned (ew Eb 34) = F) by (rewrite OLDb by lia; exact U34a).
  assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb by lia; exact U32a).
  assert (U241b : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U241).
  assert (U242b : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U242).
  assert (U273b : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U273).
  match type of HS3 with ?A1 -> ?A2 -> _ => assert (HD1 : A1); [|assert (HD2 : A2); [|specialize (HS3 HD1 HD2)]] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_fregion, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128. rewrite U39b, U2b, U34b, U241b, U242b, U273b, U32b.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128.
    rewrite U513, U39b, U2b, U34b, U241b, U242b, U273b, U32b.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd8a. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Hd8b.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as Hd8c.
    unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  clear HS. rename HS3 into HS. norm_ss HS.
  (* run 2 (plain): the frame's slot F+184, the fake frame's header and its shadow's poison *)
  paj_run_sh RUNP HS HJ2.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U242b, ?U273b, ?U32b in Hr;
        first [ lia
        | left; lia
        | right; right; right; exists 1, fpos; split; [left; reflexivity|];
          change (frame_addr ly 1 fpos) with FF; change (fs_frame_bytes 1) with 128;
          first [ left; unfold in_zr; cbn [fst snd]; lia
          | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hin'. }
  (* the size refusal: n >> 26 <> 0 goes to 0x84d7c; refuted by the contract's n < 2^26 *)
  assert (E11b : ew Eb 11 = Z_to_bv 64 n) by (rewrite OLDb, OLDa, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity).
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ne_U, U_SAlu, (U_atom Eb 11 n E11b), !U_SLit in Hc by lia. cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 26) 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
    vm_compute in Hc. discriminate Hc. }
  (* the fake frame and its shadow become read-only (the token run keeps its windows off the shadow span);
     the runtime's GOT and uar regions are dropped *)
  pro_keep HS [0; 1; 2; 3; 4]%nat.
  pro_ro HS 0%nat. pro_ro HS 1%nat.
  pose proof pro_vals as (PV67 & PV68 & PV69 & PV70 & PV71 & PV72 & PV73 & PV74 & PV75 & PV76 & PV77 & PV78 &
    PVO22 & PVO25 & PVO26 & PVO0 & PVO32).
  assert (RGv : rg_client fr_RG = 0xa1fe0 /\ rg_client_broken fr_RG = 0x5d87e0 /\ rg_send_max fr_RG = 0x5d8840 /\
    rg_gone fr_RG = 0x5d8860 /\ rg_send_dead fr_RG = 0x5d8880 /\ rg_send_eintr fr_RG = 0x5d88a0 /\
    rg_s fr_RG = 0x5d88e0 /\ rg_nout fr_RG = 0x5d88c0 /\ rg_nsrc fr_RG = 0x5d87a0 /\ rg_src fr_RG = 0x5d87c0)
    by (vm_compute; repeat split; reflexivity).
  destruct RGv as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
  assert (HNFDv : A_NFD = 0x5d8820) by reflexivity.
  (* the seven global stores' regions (pr_g 67 .. 73), all in G_fr *)
  pro_addg HS HEIb 67%nat (-512) 4 HG_client.
  pro_addg HS HEIb 68%nat 1528 1 HG_cbroken.
  pro_addg HS HEIb 69%nat 1588 4 HG_nfd.
  pro_addg HS HEIb 70%nat 1616 8 HG_smax.
  pro_addg HS HEIb 71%nat 1636 1 HG_gone.
  pro_addg HS HEIb 72%nat 1660 1 HG_sdead.
  pro_addg HS HEIb 73%nat 1684 1 HG_seintr.
  pro_addf HS HEIb 347%nat. pro_addf HS HEIb 348%nat. pro_addf HS HEIb 349%nat. pro_addf HS HEIb 350%nat.
  pro_addf HS HEIb 351%nat. pro_addf HS HEIb 352%nat. pro_addf HS HEIb 353%nat.
  (* the journal, from here at G_fr (the donor's journal is ajournal_gx at G = [], lifted) *)
  pose proof (ajournal_gx_G_mono segs B [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ2)) as HJ3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOKb : sh_ok segs Bx [] Eb (mrestrict (w_H W) (ms_mem msx))) by (unfold sh_ok; constructor) end.
  pose proof (pro_Fb (LFCX ly S W regs mem md p n pl M) HB) as (HFlo & HFsp & HFsp2 & _ & _ & _).
  change (lf_F (LFCX ly S W regs mem md p n pl M)) with F in HFlo, HFsp, HFsp2. unfold CEIL8 in HFlo.
  cbn [c_regs] in HFsp, HFsp2.
  (* run 3: the frame's slots and the seven globals, to `jal op_add` *)
  paj_run_to_tok RUNTOX HS HJ3 SHOKb Bspan AF_fr_op_add.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U242b, ?U273b, ?U32b in Hr;
        pro_imgh HEIb Hr;
        first [ clear - Hr; lia
        | left; split; [left; clear - Hr WS HFsp HFsp2; lia | clear - Hr; lia]
        | right; left; first [ apply HG_client; clear - Hr RG1; lia | apply HG_cbroken; clear - Hr RG2; lia
                             | apply HG_nfd; clear - Hr HNFDv; lia | apply HG_smax; clear - Hr RG3; lia
                             | apply HG_gone; clear - Hr RG4; lia | apply HG_sdead; clear - Hr RG5; lia
                             | apply HG_seintr; clear - Hr RG6; lia ]
        ]
      | ]).
    destruct Hin'. }
  (* ---- the bytes the prologue keeps from the entry to the call (pro_mid's KEEP) ---- *)
  pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    rename Hx into HFr3;
    assert (K3 : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= FF \/ FF + 128 <= a) ->
        (a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a) -> pro_gst_out a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a) end.
  { clear - HFr3 HFr0 HEIb U2b U34b U39b U512 U513 U241b U242b U273b U32b HFlo HFsp.
    intros a Ha Hff Hsh Hgst. pose proof Hgst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7). clear Hgst.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj1 (pro_kept_frame _ _ W _ _ a HFr3 ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEIb Ha HFlo HFsp))).
    pose proof (proj1 (pro_kept_frame _ _ W _ _ a HFr0 ltac:(clear - Ha D1; lia)
      ltac:(pro_nwr_k HEIb Ha HFlo HFsp))) as K2.
    cbn [ms_mem mkst] in K2. exact K2. }
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { clear - HFr HEI Usp UF HFlo HFsp.
    intros a Ha. pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    exact (proj1 (pro_kept_frame _ _ W _ _ a HFr ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEI Ha HFlo HFsp))). }
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    assert (KEEP : forall a, pro_ks (LFCX ly S W regs mem md p n pl M) a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem a) end.
  { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5). unfold off_img in HFimg.
    intros a [Ha | (p0 & n0 & Hp & Hpa)]; [|cbn [c_ly c_S] in Hp].
    - pose proof (G_obj_rng a (G_keep_obj a Ha)) as Hr. pose proof (G_keep_gst a Ha) as Hg.
      destruct (HG a (HG_obj a (G_keep_obj a Ha))) as (Him & Hno & _).
      rewrite (K3 a ltac:(clear - Hr D1; lia) ltac:(clear - Hr HFimg; lia) ltac:(clear - Hr HF4096; lia) Hg),
        (HK3 a Him Hno (G_obj_err a (G_keep_obj a Ha))).
      exact (K1 a ltac:(clear - Hr D1; lia)).
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HARa Hp) as (_ & H4096 & Hbc & Happ & _).
      assert (Hp2 : In (p0, n0) (ablocks B ly S2)) by (rewrite Eab; exact Hp).
      pose proof (pro_blk_frm _ _ _ _ _ p0 n0 1 fpos HARb Hp2 Hfin2) as Hd.
      change (frame_addr ly 1 fpos) with FF in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      assert (Hsh : a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a).
      { destruct (Z_lt_le_dec a (2147450880 + FF / 8)) as [Hl | Hl]; [left; exact Hl | right].
        destruct (Z_lt_le_dec a (2147450880 + FF / 8 + 16)) as [Hl2 | Hl2]; [|exact Hl2].
        exfalso. exact (fshadow_not_app FF 16 p0 (req_size n0) a ltac:(clear - HF4096; lia)
          ltac:(clear - HFceil D1; lia) Happ ltac:(clear - Hl Hl2; lia) Hpa). }
      rewrite (K3 a ltac:(clear - H4096 Hbc Hpa; lia) ltac:(clear - Hd Hpa; lia) Hsh
        (pro_blk_gst _ _ _ _ _ p0 n0 a HARa Hp Hpa)).
      replace a with (p0 + (a - p0)) by ring.
      rewrite (HK2 p0 n0 (a - p0) Hp ltac:(clear - Hpa; lia) (fun Hf => Hf)).
      exact (K1 (p0 + (a - p0)) ltac:(clear - H4096 Hbc Hpa D1; lia)). }
  (* ---- op_add's entry ---- *)
  pmkst HS.
  pro_rgn HS 0%nat RQ7. pro_rgn HS 1%nat RQ6. pro_rgn HS 2%nat RQ5. pro_rgn HS 3%nat RQ4.
  pro_rgn HS 4%nat RQ3. pro_rgn HS 5%nat RQ2. pro_rgn HS 6%nat RQ1. pro_rgn HS 7%nat RQS.
  pro_rgn HS 8%nat RQF. pro_rgn HS 10%nat RQV. pro_rgn HS 11%nat RQP.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
  assert (EAb : forall r, (r < 32)%nat -> ew Eb r = getr regs (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. rewrite OLDb, OLDa by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. change (bv_modulus 5) with 32. clear - Hr; lia. }
  assert (Hfrs2' : frames S2 = [(1, fpos)]) by (rewrite Hfrs2, Hfrs; reflexivity).
  exact (pro_at_call (LFCX ly S W regs mem md p n pl M) S2 0 fpos Eb _ _ _ HB HJ3 Eab Hfrs2' Hnev2 Hbb2 HEIb
    U2b U34b U39b U513 (eq_trans (OLDb 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33a) U512 EAb
    RQ7 RQ6 RQ5 RQ4 RQ3 RQ2 RQ1 RQS RQF RQV RQP Q1 Q2 Q3 Q4 Q8 Q9 Q21 Q22 Q24 Q26 KEEP).
Qed.
End pro.
