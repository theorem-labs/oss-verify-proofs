(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 616 of its 671 lines of code are new or changed and 398 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_KMOD: the piece from MK_FEXIT 0x86864 (the fold is done)
   to MK_REFUSE 0x86cc0 / MK_CPY 0x86880, over lib/A/Prog/m_file_s_kmod_m.v's cut statements. The KMOD catalogue-row sub-lane
   of the G2 walk owner's G2.

   THE CODE (dis/m_file.fuzz_segconf.asan.s:620-626; 6 instructions and one call):
     86864 ld s5,152(s1)          s5 = low = FB + 32 (the spill slot mf_cells names)
     86868 add a0,s5,s4           a0 = low + ln, ln = mk_ln vl = min(vl, 23) in s4
     8686c sb zero,0(a0)          low[ln] = 0, with NO instrumented check (ln <= 23, so the byte is inside
                                  low.i, a byte of the walk's own side-stack frame)
     86870 mv a0,s5               a0 = low
     86874 mv a1,s4               a1 = ln
     86878 jal fuzz_catalogue_row the call (SIGMA SS_fuzz_catalogue_row = BASE + AF_fuzz_catalogue_row by SIGP)
     8687c beqz a0,86cc0          a0 = 0 (no row) goes to MK_REFUSE, else falls through to MK_CPY 0x86880

   HOW THE STORE IS RESOLVED. The seed (lib/A/Prog/m_file_sd.v mf_seed) keeps low.i as one region based on the
   frame atom 34, so the store's address, the symbolic sum `SAlu ALU_ADD (SOff 34 32) (SOff 20 0)` (the slot's
   value plus s4's own atom), is not of the form `atom + literal` and the executor cannot place it. Instead of a
   case split on the 24 values of ln, this walk drops the low.i region and closes the spill slots' write window
   (one st_ok_pi_submem, submemb_sound: the run reads slot 152 and writes no slot, and a closed window is what
   carries mf_cells and mf_np across the run), and adds a one-byte region at a fresh atom (the seed's xs list,
   atom 52) whose value is FB + 32 + ln, with the alias `SAlu ALU_ADD (SOff 34 32) (SOff 20 0) = SOff 52 0`
   (st_ok_pi_add_alias). `aliased2` then rewrites the sum to `SOff 52 0`, the store lands in that region, and it
   is the run's only write window; every other byte is kept (kept_of_frame), so the fold's bytes and the cut's
   cells survive to the call (m_file_k.v's mf_keep_run_s, whose mf_rw covers low.i).

   THE BRANCH at 0x8687c is decided without a case split on the row index: the walk is seeded again at the return
   point and, on the `Some r` arm, atom 10 (a0's own atom) is given the fact that its value lies in
   [catA, catA + 0x128 * 10] (st_ok_pi_add_fact), so the executor's interval test decides `beqz` false; on the
   `None` arm a0 is pinned to the literal 0 (st_ok_pi_pin_reg').

   The call's premises come from the cut's own facts: the bytes are `seg_spec.zb (h_fold vv 24)` (mkb_zs_bytes:
   sa_zs at the reader gives sa_bytes of zb and seg_spec.zs (zb l) = l, so the contract's answer
   cat_ptr catA (cat_row (zs sb)) is cat_ptr catA (cat_row (h_fold vv 24))); sa_addr and sa_loc are properties of
   low.i, proved here from mf_core's zero shadow bytes for low.i (MF_LOW_ON) and AR's frame laws. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_sd m_file_k m_file_s_kmod_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x8687c, the return point of the call at 0x86878 (MK_CPY is the next instruction, 0x86880) *)
Definition MK_RET : Z := AF_m_file + 0x9c0.

(* the seed's spill-slot region with its write window closed: the run reads slot 152 and writes no slot *)
Definition mkb_slots_ro : YP09.region :=
YP09.mkRegion (Some 2%nat) 24 160 0 0 (YP09.r_chunks (mf_r_slots true false [])).
(* the regions of the store run: the seed's, without low.i and with the slots read-only *)
Definition mkb_regions : smem :=
[mf_r_saved; mkb_slots_ro; mf_r_fh false; mf_r_ft; mf_r_fs false MF_LOW_ON].
(* the regions of the branch run: every window closed, so the run writes nothing *)
Definition mkb_regions_b : smem :=
[mf_r_saved; mkb_slots_ro; mf_r_fh false; mf_r_low false []; mf_r_ft; mf_r_fs false MF_LOW_ON].
(* the one-byte region the store writes, at the seed's extra atom 52 = FB + 32 + ln *)
Definition mkb_low_reg : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 1 [].

(* ================================ pure: the value and the fold ================================ *)
Lemma mkb_break_fst_len : forall p, (length (fst (break_nl p)) <= length p)%nat.
Proof.
induction p as [|b p IH]; cbn; [lia|].
destruct (b =? NL); cbn; [lia|]. destruct (break_nl p) as [l q]; cbn in *; lia.
Qed.

(* the value's length: mk_base fixes vv as the vl bytes at ov, inside the line *)
Lemma mkb_vv_len : forall rest ov vl vv,
(ov + vl <= length (mf_line rest))%nat -> firstn vl (skipn ov rest) = vv -> length vv = vl.
Proof.
intros rest ov vl vv Hle <-. rewrite length_firstn, length_skipn.
pose proof (mkb_break_fst_len rest) as Hb. unfold mf_line in Hle. lia.
Qed.

Lemma mkb_le_byte_1 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof.
intros z Hz. assert (E : le_byte z 1 0 = (z mod 256) mod 256) by reflexivity.
rewrite E, Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.

(* one byte more at the end of a byte run *)
Lemma mkb_zs_snoc : forall (rd : reader) a l z,
sa_zs rd a l -> rd (a + Z.of_nat (length l)) = Some z -> sa_zs rd a (l ++ [z]).
Proof.
intros rd a l z H Hz i Hi. rewrite length_app in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i (length l)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. exact (H i Hl).
- replace i with (length l) by lia. rewrite nth_middle. exact Hz.
Qed.

(* the symbolic state as a literal, so the executor's vm_compute sees it *)
Ltac mkb_norm HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss _ => let w := eval vm_compute in ss in change ss with w in HS
| st_ok _ _ ?ss _ => let w := eval vm_compute in ss in change ss with w in HS
end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a one-byte cell of the restricted memory, through the ASan reader *)
Lemma mkb_rd_of_val1 : forall (W : world SEGS) mem a z, 0 <= z < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) a 1 z -> rdW W mem a = Some z.
Proof.
intros W mem a z Hz H. pose proof (H 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E.
unfold aview. rewrite E. cbn [option_map]. f_equal.
lazymatch goal with |- bv_unsigned (Z_to_bv 8 ?t) = z =>
  assert (Ht : t = z);
  [ assert (E2 : t = (z mod 256) mod 256) by reflexivity;
    rewrite E2, Z.mod_mod by lia; apply Z.mod_small; lia
  | rewrite Ht ] end.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* every byte a reader answers lies in [0, 256) *)
Lemma mkb_zs_range : forall (W : world SEGS) mem a l, sa_zs (rdW W mem) a l ->
Forall (fun z => 0 <= z < 256) l.
Proof.
intros W mem a l H. apply Forall_forall. intros z Hz.
destruct (In_nth l z 0 Hz) as (i & Hi & Hn).
pose proof (H i Hi) as E. rewrite Hn in E. exact (sa_aview_rng _ _ _ _ _ E).
Qed.

(* the call's byte list: sa_zs of a text gives sa_bytes of its seg_spec.zb, whose seg_spec.zs is the text again *)
Lemma mkb_zs_bytes : forall (W : world SEGS) mem a l, sa_zs (rdW W mem) a l ->
sa_bytes (rdW W mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l /\
length (seg_spec.zb l) = length l.
Proof.
intros W mem a l H.
pose proof (mkb_zs_range W mem a l H) as HF.
split; [|split].
- intros i Hi. unfold seg_spec.zb in Hi |- *. rewrite length_map in Hi.
  unfold ZB0. rewrite (map_nth (Z_to_bv 8) l 0 i).
  rewrite (H i Hi). f_equal.
  rewrite Forall_forall in HF. pose proof (HF (nth i l 0) (nth_In l 0 Hi)) as Hr.
  rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
- exact (sa_zs_zb l HF).
- unfold seg_spec.zb. apply length_map.
Qed.

(* a byte run carried across a change that keeps every byte of its range *)
Lemma mkb_zs_keep : forall (rd rd' : reader) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l K H i Hi. rewrite K by lia. exact (H i Hi). Qed.

Section e.
Variable B : asyms.
(* the shared Section hypotheses (the m_file cut-statement lane's list, CALLS-CONTEXT.md) *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis FCR : forall fx0 : YK11.FPState,
  fuzz_catalogue_row_contract (fx := fx0) SEGS B (BASE + AF_fuzz_catalogue_row)
    SegInstA.STK_fuzz_catalogue_row SegInstA.RLO_A SegInstA.RHI_A SegInstA.catA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* =============================== the frame and the low buffer =============================== *)
(* what AR gives about the walk's own side-stack frame at a mid-walk state *)
Lemma mkb_frame : forall v lyc Sc Wc memc mdc pos lowsh mcc,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
In (1, pos) (frames Sc) /\ frame_addr lyc 1 pos mod 32 = 0 /\ 4096 <= frame_addr lyc 1 pos /\
frame_addr lyc 1 pos + 128 <= alloc_ceiling /\ in_app (frame_addr lyc 1 pos) 128 /\
(forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> apresent (w_H Wc) memc a) /\
(forall i, 0 <= i < 16 -> apresent (w_H Wc) memc (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i)).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CORE.
pose proof CORE as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFceil, HFpres, HFSpres.
split; [exact Hfin|]. split; [exact HFal|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFapp|].
split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
intros i Hi. unfold shadow_addr in HFSpres.
exact (proj1 (HFSpres i ltac:(change (128 / 8) with 16; lia))).
Qed.

(* a frame byte is not a shadow byte of that frame *)
Lemma mkb_shadow_ne : forall v lyc Sc Wc memc mdc pos lowsh mcc i j,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> 0 <= i < 16 -> 0 <= j < 128 ->
SHADOW_OFF + frame_addr lyc 1 pos / 8 + i <> frame_addr lyc 1 pos + j.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc i j CORE Hi Hj.
destruct (mkb_frame v lyc Sc Wc memc mdc pos lowsh mcc CORE)
  as (_ & _ & HF4096 & HFceil & HFapp & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* low.i is addressable: its 8 shadow bytes are 0 at the K cuts (MF_LOW_ON), and the frame's 16 shadow bytes
   are mapped *)
Lemma mkb_low_addr : forall v lyc Sc Wc memc mdc pos mcc n,
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> 0 <= n <= 64 ->
sa_addr (rdW Wc memc) (frame_addr lyc 1 pos + 32) n.
Proof.
intros v lyc Sc Wc memc mdc pos mcc n CORE Hn.
destruct (mkb_frame v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE)
  as (Hfin & HFal & HF4096 & HFceil & HFapp & HFpres & HFSpres).
pose proof CORE as (_ & _ & _ & VSH & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc 1 pos) in *.
assert (HSB : SHADOW_OFF = 2147450880) by reflexivity.
assert (Hq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (H8 : F / 8 = 4 * (F / 32)).
{ rewrite Hq at 1. replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia. apply Z.div_mul. lia. }
assert (Hq0 : 0 <= F / 32) by (apply Z.div_pos; lia).
assert (HZ : zero_shadow (rdW Wc memc) SHADOW_OFF (F + 32) 64).
{ intros i Hi. unfold shadow_of_addr.
  replace (F + 32) with (F + 4 * 8) by lia. rewrite Z.div_add by lia.
  replace (SHADOW_OFF + (F / 8 + 4) + i) with (SHADOW_OFF + F / 8 + (4 + i)) by lia.
  apply (mkb_rd_of_val1 Wc memc _ MF_LOW_ON ltac:(unfold MF_LOW_ON; lia)).
  apply VSH. change (64 / 8) with 8 in Hi. lia. }
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (F + 32) 64).
{ apply zero_shadow_range; [| reflexivity | exact HZ].
  replace (F + 32) with ((4 * (F / 32) + 4) * 8) by lia. apply Z_mod_mult. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold sa_addr, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
split; [lia|]. split; [lia|]. split; [lia|].
split; [intros x Hx; apply HRA; lia|].
intros Hn0 s Hs. unfold shadow_addr in Hs.
replace (F + 32) with (F + 4 * 8) in Hs by lia. rewrite (Z.div_add F 4 8 ltac:(lia)) in Hs.
replace (F + 4 * 8 + n - 1) with (4 * (F / 32) * 8 + (31 + n)) in Hs by lia.
rewrite (Z.div_add_l (4 * (F / 32)) 8 (31 + n) ltac:(lia)) in Hs.
assert (Hk : 4 <= (31 + n) / 8 <= 11).
{ pose proof (Z.div_mod (31 + n) 8 ltac:(lia)) as Hd31.
  pose proof (Z.mod_pos_bound (31 + n) 8 ltac:(lia)) as Hm31. lia. }
set (k := (31 + n) / 8) in *.
assert (Hs2 : SHADOW_OFF + F / 8 <= s < SHADOW_OFF + F / 8 + 16).
{ pose proof (Z.div_mod (F / 32) 2 ltac:(lia)).
  pose proof (Z.mod_pos_bound (F / 32) 2 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (F / 8 + 4)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (F / 8 + 4)) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (4 * (F / 32) + k)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (4 * (F / 32) + k)) 8 ltac:(lia)).
  rewrite HSB in *. lia. }
apply (aview_some_of_apresent SEGS (w_H Wc) memc s).
replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
apply HFSpres. lia.
Qed.

(* low.i lies in the walk's own side-stack frame *)
Lemma mkb_low_loc : forall v lyc Sc Wc memc mdc pos lowsh mcc n,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> 0 <= n <= 96 ->
sa_loc SEGS B lyc Sc (frame_addr lyc 1 pos + 32) n.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc n CORE Hn.
destruct (mkb_frame v lyc Sc Wc memc mdc pos lowsh mcc CORE) as (Hfin & _).
right; left. exists 1, pos. split; [exact Hfin|]. split; [lia|].
change (fs_frame_bytes 1) with 128. lia.
Qed.

(* a byte of the frame is a byte the walk may write (the journal owns the frame) *)
Lemma mkb_awr_frame : forall lyc pos (STK sp0 : Z) FP bl0 blc fr0 a,
frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 ->
awr_byte SEGS B STK sp0 FP bl0 blc fr0 lyc [(1, pos)] a.
Proof.
intros lyc pos STK sp0 FP bl0 blc fr0 a Ha.
right; right; right; left. exists 1, pos. split; [left; reflexivity|].
left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
Qed.

(* the mconf block's bytes and the frame are apart (through mf_win, which holds low.i) *)
Lemma mkb_blk_ne : forall v lyc Sc Wc memc mdc pos lowsh mcc a j,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE -> 0 <= j < 96 -> a <> frame_addr lyc 1 pos + j.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc a j CX0 CORE Ha Hj.
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (b & m & Hb & Hb1 & Hb2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
intros Heq.
apply (mf_block_apart B lyc Sc Wc memc mdc pos b m a HAR Hfin Hb ltac:(lia)).
left. rewrite Heq. lia.
Qed.

(* the stack numbers at a cut: s1 = sp0 - 288 or - 304, the callee's window above the frame *)
Lemma mkb_stack : forall v, mf_cx B v ->
(mf_s1 (mv_sp v) = mv_sp v - 288 \/ mf_s1 (mv_sp v) = mv_sp v - 304) /\
alloc_ceiling + 8560 <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\ (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0.
Proof.
intros v CX0.
destruct (mf_s1_facts B v CX0) as (H1 & _ & H3).
destruct (mf_sp0 B v CX0) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1, H3.
split; [exact H1|]. split; [lia|]. split; [lia|].
destruct H1 as [H1|H1]; rewrite H1;
  [replace (mv_sp v - 288 - mv_sp v) with (-18 * 16) by lia | replace (mv_sp v - 304 - mv_sp v) with (-19 * 16) by lia];
  apply Z_mod_mult.
Qed.

(* =============================== 0x86864 .. 0x86878: the call =============================== *)
(* the six instructions and the call, with the state at the return point 0x8687c as the continuation *)
Lemma mkb_call : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv,
mf_cx B v -> mf_ls v lyc Sc ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mf_np v memc Wc (mf_next p rest) ->
(ov + vl <= length (mf_line rest))%nat -> firstn vl (skipn ov rest) = vv ->
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) (h_fold vv 24) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln vl)) ->
getr regs1 22 = w64 (line + 1) -> getr regs1 24 = w64 (frame_addr lyc 1 pos) ->
(forall S2 (W2 : world SEGS) regs2 mem2 md2,
   mf_ls v lyc S2 -> mf_core B v lyc S2 W2 mem2 md2 pos MF_LOW_ON mcc ->
   mf_cells v lyc pos mem2 W2 (Some gi) -> mf_regs_at B v lyc pos regs2 ->
   mf_loop v W2 mem2 mcc (Some gi) line p rest -> mf_np v mem2 W2 (mf_next p rest) ->
   sa_zs (rdW W2 mem2) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0]) ->
   getr regs2 10 = w64 (seg_spec.cat_ptr SegInstA.catA (cat_row (h_fold vv 24))) ->
   getr regs2 20 = w64 (Z.of_nat (mk_ln vl)) -> getr regs2 21 = w64 (frame_addr lyc 1 pos + 32) ->
   getr regs2 22 = w64 (line + 1) -> getr regs2 24 = w64 (frame_addr lyc 1 pos) ->
   SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + MK_RET)) mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + MK_FEXIT)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv
  CX0 LS CORE CELLS RAT LOOP NP Hovvl Hvv HZS H20 H22 H24 HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
destruct (mk_ln_bound vl) as (Hln23 & Hlnvl & _).
assert (Hvvlen : length vv = vl) by exact (mkb_vv_len rest ov vl vv Hovvl Hvv).
assert (Hhf : length (h_fold vv 24) = mk_ln vl) by (rewrite hfold_len, Hvvlen; reflexivity).
destruct (mkb_frame v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE)
  as (Hfin & HFal & HF4096 & HFceil & HFapp & HFpres & HFSpres).
destruct (mkb_stack v CX0) as (Hs1c & Hsp1 & Hsp47 & Ho16).
assert (HSTK1 : SegInstA.STK_fuzz_catalogue_row = 8256) by reflexivity.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Hgi : (gi < length (mc_seg mcc))%nat) by (pose proof LOOP as (_ & _ & _ & _ & _ & Hc & _); exact Hc).
assert (Hseg32 : (length (mc_seg mcc) <= 32)%nat)
  by (pose proof CORE as (_ & _ & _ & _ & _ & _ & (bs & _ & Henc) & _); exact (proj1 (proj2 Henc))).
assert (Hcrange : 0 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= 2 ^ 63)
  by (pose proof CORE as (_ & _ & _ & _ & _ & _ & _ & (A1 & A2 & _) & _); lia).
unfold seg_spec.SEG_M_SIZE in Hcrange.
assert (Hcurb : 0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64).
{ unfold mf_cur_ptr, seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia. }
pose proof RAT as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
(* the seed at 0x86864, with the store's destination as the extra atom 52 *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) 0
  [frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)] MK_FEXIT true false [] false false [] false
  CX0 CORE (mf_regs_base_of B v lyc pos regs1 RAT) (fun _ => CELLS) Hcurb
  ltac:(intros HH; discriminate HH) ltac:(lia) ltac:(unfold MF_LOW_ON; lia)
  ltac:(apply Forall_nil) ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity)) as HS.
set (XS := [frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)]) in *.
set (E := mfE regs1 v lyc pos (Some gi) 0 XS) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros k r Hk; unfold E; apply mfE_reg; exact Hk).
assert (EX : forall j, (32 + j < A_TEXT)%nat ->
  ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 XS) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; apply mfE_extra; exact Hj).
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E32, E34, E36.

assert (E52 : ew E 52 = Z_to_bv 64 (frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl))).
{ replace 52%nat with (52 + 0)%nat by reflexivity. unfold E.
  rewrite (mfE_xs regs1 v lyc pos (Some gi) 0 XS 0 ltac:(unfold A_TEXT; lia)). unfold XS. reflexivity. }
assert (HFdiv : 0 <= frame_addr lyc 1 pos / 8 <= 2 ^ 44).
{ pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)). lia. }
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U52 : bv_unsigned (ew E 52) = frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl))
  by (rewrite E52; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = w64 (Z.of_nat (mk_ln vl)))
  by (rewrite (EE 20%nat (20%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H20).
assert (U20 : bv_unsigned (ew E 20) = Z.of_nat (mk_ln vl))
  by (rewrite E20; unfold w64; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)).
{ rewrite (EE 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity)), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (U8 : bv_unsigned (ew E 8) = mv_sp v).
{ rewrite (EE 8%nat (8%bv : bv 5) ltac:(vm_compute; reflexivity)), R8. unfold w64.
  apply unsigned_lit_small. lia. }
(* the alias that places the store: low + ln is the atom 52 *)
assert (HAL : sv_denot E (SAlu ALU_ADD (SOff 34 32) (SOff 20 0)) = sv_denot E (SOff 52 0)).
{ cbn [sv_denot]. rewrite U34, U20, U52, !Z.add_0_r, alu64_add_lit. f_equal; lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
(* drop low.i, close the slot window, add the one-byte region and the alias *)
pose proof (st_ok_pi_submem E _ _ mkb_regions HS
  ltac:(apply submemb_sound; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS1.
clear HS. mkb_norm HS1.
assert (HROK : YP09.region_ok SEGS E (mrestrict (w_H Wc) memc) mkb_low_reg).
{ unfold mkb_low_reg, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U52. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply HFpres. lia. }
assert (HDISJ : all_disjoint E mkb_low_reg mkb_regions).
{ apply all_disjoint_of_extents.
  unfold mkb_low_reg, mkb_regions, mkb_slots_ro, mf_r_saved, mf_r_slots, mf_r_fh, mf_r_ft, mf_r_fs,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U52, U2, U8, U34, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SHADOW_OFF in *. repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ mkb_low_reg HS1 ltac:(vm_compute; reflexivity) HROK HDISJ) as HS2.
clear HS1. mkb_norm HS2.
pose proof (st_ok_pi_add_alias E _ _ (SAlu ALU_ADD (SOff 34 32) (SOff 20 0)) (SOff 52 0) HS2 HAL) as HS3.
clear HS2. mkb_norm HS3.
pose proof (proj1 CORE) as HJ.
paj_run_shc RUNP RUNC HS3 HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 52%nat
    (frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)));
  [ reflexivity | exact U52
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply mkb_awr_frame; lia |];
  do 5 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil. }
pmkst HS3.
assert (SIG_FCR : SIGMA SS_fuzz_catalogue_row = BASE + AF_fuzz_catalogue_row).
{ rewrite (SIGP SS_fuzz_catalogue_row
    ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  f_equal; vm_compute; reflexivity. }
rewrite SIG_FCR.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in * end.
prreg HS3 (1%bv : bv 5) Q1. prreg HS3 (2%bv : bv 5) Q2. prreg HS3 (3%bv : bv 5) Q3.
prreg HS3 (4%bv : bv 5) Q4. prreg HS3 (8%bv : bv 5) Q8. prreg HS3 (9%bv : bv 5) Q9.
prreg HS3 (10%bv : bv 5) Q10. prreg HS3 (11%bv : bv 5) Q11. prreg HS3 (18%bv : bv 5) Q18.
prreg HS3 (19%bv : bv 5) Q19. prreg HS3 (20%bv : bv 5) Q20. prreg HS3 (21%bv : bv 5) Q21.
prreg HS3 (22%bv : bv 5) Q22. prreg HS3 (24%bv : bv 5) Q24. prreg HS3 (25%bv : bv 5) Q25.
prreg HS3 (26%bv : bv 5) Q26.
(* the run wrote one byte: low[ln] *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> a <> frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
    (fun x => x = frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)) HFr _ a Ha Hne).
  intros b wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hr;
      first [ rewrite U52 in Hr; lia | lia ] |]).
  destruct Hin. }
assert (RWok : forall a, (fun x => x = frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)) a ->
  mf_rw v lyc pos a) by (intros a ->; unfold mf_rw; right; right; left; lia).
assert (RWS : mf_rws v (fun x => x = frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)))
  by (intros a -> Hin; exfalso; lia).
assert (VSH2 : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_ON).
{ intros i Hi. pose proof CORE as (_ & _ & _ & VSH & _).
  apply (mf_val_keep Wc Wc memc (ms_mem ms) _ _ 1%nat _ KEEP1);
  [ unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
  | intros k Hk; change (Z.of_nat 1) with 1 in Hk;
    pose proof (mkb_shadow_ne v lyc Sc Wc memc mdc pos MF_LOW_ON mcc i
      (32 + Z.of_nat (mk_ln vl)) CORE ltac:(lia) ltac:(lia)); lia
  | exact (VSH i Hi) ]. }
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (mf_s1 (mv_sp v) + 136) 8
  (mf_cur_ptr (mv_c v) (Some gi)))
  by (apply (mf_val_keep Wc Wc memc (ms_mem ms) _ _ 8%nat _ KEEP1);
      [lia | change (Z.of_nat 8) with 8; lia
      | intros k Hk; change (Z.of_nat 8) with 8 in Hk; lia | exact V136]).
pose proof CORE as (_ & _ & _ & _ & _ & _ & HMC & _).
assert (MC2 : sa_mconf (rdW Wc (ms_mem ms)) (mv_c v) mcc).
{ apply (mf_mconf_keep Wc Wc memc (ms_mem ms) _ (mv_c v) mcc KEEP1);
  [ lia | unfold seg_spec.SEG_M_SIZE; lia | | exact HMC ].
  intros a Ha.
  pose proof (mkb_blk_ne v lyc Sc Wc memc mdc pos MF_LOW_ON mcc a (32 + Z.of_nat (mk_ln vl))
    CX0 CORE Ha ltac:(lia)) as Hne. lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq
  (fun x => x = frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)) MF_LOW_ON (Some gi) mcc
  CX0 CORE CELLS HJ KEEP1 RWok RWS VSH2 V136' MC2) as (CORE2 & CELLS2 & LOOPK).
assert (NP2 : mf_np v (ms_mem ms) Wc (mf_next p rest)).
{ unfold mf_np in NP |- *.
  apply (mf_val_keep Wc Wc memc (ms_mem ms) _ _ 8%nat _ KEEP1);
  [lia | change (Z.of_nat 8) with 8; lia
  | intros k Hk; change (Z.of_nat 8) with 8 in Hk; lia | exact NP]. }
assert (HZS2 : sa_zs (rdW Wc (ms_mem ms)) (frame_addr lyc 1 pos + 32) (h_fold vv 24)).
{ apply (mkb_zs_keep (rdW Wc memc)); [| exact HZS].
  intros x Hx. rewrite Hhf in Hx. apply KEEP1; lia. }
assert (HZERO : rdW Wc (ms_mem ms) (frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)) = Some 0).
{ lazymatch type of HS3 with st_ok _ ?Ex ?ssx _ =>
    pose proof (st_ok_region_nth Ex ssx _ 0%nat _ HS3 eq_refl) as HR0 end.
  lazymatch type of HR0 with
  | YP09.region_ok _ _ _ (YP09.mkRegion (Some ?nn) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (field_of_region E _ nn _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR0 U52
      ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V0
  end.
  rewrite Z.add_0_r in V0. change (N.to_nat 1) with 1%nat in V0.
  exact (mkb_rd_of_val1 Wc (ms_mem ms) _ 0 ltac:(lia) V0). }
assert (RAT2 : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RAT);
  [ rewrite Q2; apply (EE 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity))
  | rewrite Q3; apply (EE 3%nat (3%bv : bv 5) ltac:(vm_compute; reflexivity))
  | rewrite Q4; apply (EE 4%nat (4%bv : bv 5) ltac:(vm_compute; reflexivity))
  | rewrite Q8; apply (EE 8%nat (8%bv : bv 5) ltac:(vm_compute; reflexivity))
  | rewrite Q9, (EE 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity)), R2, R9; reflexivity
  | rewrite Q18, E32, R18; reflexivity
  | rewrite Q19; apply (EE 19%nat (19%bv : bv 5) ltac:(vm_compute; reflexivity))
  | rewrite Q25; apply (EE 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity))
  | rewrite Q26; apply (EE 26%nat (26%bv : bv 5) ltac:(vm_compute; reflexivity)) ]. }
assert (Hsp : spZ (ms_regs ms) = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)).
{ unfold spZ. rewrite Q2, (EE 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity)), R2. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
destruct (mf_chain_at B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (ms_regs ms) CX0 CORE2 RAT2)
  as (ch1 & CH).
assert (Q1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + MK_RET))
  by (rewrite Q1; f_equal; unfold MK_RET, AF_m_file; lia).
destruct (mkb_zs_bytes Wc (ms_mem ms) (frame_addr lyc 1 pos + 32) (h_fold vv 24) HZS2)
  as (HB & HZB & HLB).
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_fuzz_catalogue_row))
    SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
    (mv_mem v) (mv_md v) [(1, pos)] lyc Sc mdq 0 SegInstA.STK_fuzz_catalogue_row [] EV_fuzz_catalogue_row
    (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + MK_RET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (seg_spec.cat_ptr SegInstA.catA
         (cat_row (seg_spec.zs (seg_spec.zb (h_fold vv 24))))) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) SegInstA.STK_fuzz_catalogue_row (fun _ => False) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ Hsp Ho16).
  - lia.
  - rewrite HSTK1; lia.
  - rewrite HSTK, HSTK1; lia.
  - rewrite Q3, (EE 3%nat (3%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R3.
  - rewrite Q4, (EE 4%nat (4%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R4.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [unfold MK_RET, AF_m_file; lia | unfold MK_RET, AF_m_file; reflexivity].
  - rewrite unsigned_lit_small by (unfold MK_RET, AF_m_file; lia). unfold MK_RET, AF_m_file; lia.
  - replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) by lia.
    rewrite <- (mf_sp_at B v lyc pos (ms_regs ms) CX0 RAT2). exact CH.
  - intros HPRE1. eapply SRr_mono.
    + apply (FCR fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq ch1 (frame_addr lyc 1 pos + 32)
        (Z.of_nat (mk_ln vl)) (seg_spec.zb (h_fold vv 24)) HPRE1
        (mf_rod_now B RELRO v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CX0 CORE2)
        ltac:(rewrite Q10, U34; reflexivity) ltac:(lia)
        ltac:(rewrite Q11; exact E20) ltac:(lia)
        HB ltac:(rewrite HLB, Hhf; reflexivity)
        (mkb_low_addr v lyc Sc Wc (ms_mem ms) mdq pos mcc (Z.of_nat (mk_ln vl)) CORE2 ltac:(lia))
        (mkb_low_loc v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Z.of_nat (mk_ln vl)) CORE2
           ltac:(lia))
        (mf_cat_now B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CX0 CORE2)
        ltac:(pose proof (mf_nev B v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc CX0 CORE2);
              unfold EV_fuzz_catalogue_row in *; lia)).
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK2).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, Q1'; reflexivity|].
      split; [exact HJc|]. split; [exact HPr | exact HK2].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & KEPT & NOAL)).
rewrite HZB in A0.
destruct (mf_keep_call0 B v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi)
  ly3 S3 W3 regs3 mem3 md3 (0 + EV_fuzz_catalogue_row) SegInstA.STK_fuzz_catalogue_row
  CX0 CORE2 CELLS2 RAT2 HJo ltac:(reflexivity) HP3 NOAL ltac:(lia) KEPT)
  as (Ely3 & HLS3 & CORE3 & CELLS3 & RAT3 & NPK & LOOPK2).
assert (HWIN : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 ->
  ~ (spZ (ms_regs ms) - SegInstA.STK_fuzz_catalogue_row <= a < spZ (ms_regs ms))).
{ intros a Ha. rewrite (mf_sp_at B v lyc pos (ms_regs ms) CX0 RAT2), HSTK1. lia. }
assert (HZS3 : sa_zs (rdW W3 mem3) (frame_addr lyc 1 pos + 32) (h_fold vv 24 ++ [0])).
{ apply mkb_zs_snoc.
  - apply (mkb_zs_keep (rdW Wc (ms_mem ms))); [| exact HZS2].
    intros x Hx. rewrite Hhf in Hx. apply KEPT; [lia | apply HWIN; lia | intros []].
  - rewrite Hhf.
    rewrite (KEPT (frame_addr lyc 1 pos + 32 + Z.of_nat (mk_ln vl)) ltac:(lia)
      ltac:(apply HWIN; lia) ltac:(intros [])). exact HZERO. }
apply (HK S3 W3 regs3 mem3 md3 (HLS3 LS) CORE3 CELLS3 RAT3
  (LOOPK2 _ _ _ _ _ (LOOPK _ _ _ _ _ LOOP)) (NPK _ NP2) HZS3 A0).
- transitivity (getr (ms_regs ms) 20);
  [ exact (HP3 20 ltac:(unfold acallee_saved; lia))
  | rewrite Q20, (EE 20%nat (20%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H20 ].
- transitivity (getr (ms_regs ms) 21);
  [ exact (HP3 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21, U34; reflexivity ].
- transitivity (getr (ms_regs ms) 22);
  [ exact (HP3 22 ltac:(unfold acallee_saved; lia))
  | rewrite Q22, (EE 22%nat (22%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H22 ].
- transitivity (getr (ms_regs ms) 24);
  [ exact (HP3 24 ltac:(unfold acallee_saved; lia))
  | rewrite Q24, (EE 24%nat (24%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H24 ].

Qed.

(* ============================ 0x8687c: the branch on the row ============================ *)
Theorem mk_fexit_ok : forall n, MK_REFUSE_stmt B n -> MK_CPY_stmt B n -> MK_FEXIT_stmt B n.
Proof.
intros n REF CPY v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv MKB HFIN HZS H20.
pose proof MKB as (CX0 & LS & FRM & CORE & CELLS & RAT & Hlen & Hne & LOOP & Hovvl & Hvv & HNP & R24 & R22).
unfold mf_at.
apply (mkb_call v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv
  CX0 LS CORE CELLS RAT LOOP HNP Hovvl Hvv HZS H20 R22 R24).
clear CORE CELLS RAT LOOP HNP HZS H20 R22 R24 LS MKB regs1 memc mdc Wc Sc.
intros S2 W2 regs2 mem2 md2 LS2 CORE2 CELLS2 RAT2 LOOP2 NP2 HZS2 A0 H20' H21' H22' H24'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (mkb_frame v lyc S2 W2 mem2 md2 pos MF_LOW_ON mcc CORE2)
  as (Hfin & HFal & HF4096 & HFceil & HFapp & HFpres & HFSpres).
destruct (mkb_stack v CX0) as (Hs1c & Hsp1 & Hsp47 & Ho16).
assert (Hgi : (gi < length (mc_seg mcc))%nat) by (pose proof LOOP2 as (_ & _ & _ & _ & _ & Hc & _); exact Hc).
assert (Hseg32 : (length (mc_seg mcc) <= 32)%nat)
  by (pose proof CORE2 as (_ & _ & _ & _ & _ & _ & (bs & _ & Henc) & _); exact (proj1 (proj2 Henc))).
assert (Hcrange : 0 <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= 2 ^ 63)
  by (pose proof CORE2 as (_ & _ & _ & _ & _ & _ & _ & (A1 & A2 & _) & _); lia).
unfold seg_spec.SEG_M_SIZE in Hcrange.
assert (Hcurb : 0 <= mf_cur_ptr (mv_c v) (Some gi) < 2 ^ 64)
  by (unfold mf_cur_ptr, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
pose proof RAT2 as (R2b & R3b & R4b & R8b & R9b & R18b & R19b & R25b & R26b).
pose proof (mf_seed B VOBJS v lyc S2 W2 regs2 mem2 md2 pos MF_LOW_ON mcc (Some gi) 0
  (@nil Z) MK_RET true false [] false false [] false
  CX0 CORE2 (mf_regs_base_of B v lyc pos regs2 RAT2) (fun _ => CELLS2) Hcurb
  ltac:(intros HH; discriminate HH) ltac:(lia) ltac:(unfold MF_LOW_ON; lia)
  ltac:(apply Forall_nil) ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity)) as HSb.
set (Eb := mfE regs2 v lyc pos (Some gi) 0 (@nil Z)) in *.
assert (HEIb : img_env VAL A_LIM Eb) by (unfold Eb, mfE; apply Eimg_env).
assert (EEb : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew Eb k = getr regs2 r)
  by (intros k r Hk; unfold Eb; apply mfE_reg; exact Hk).
assert (EXb : forall j, (32 + j < A_TEXT)%nat ->
  ew Eb (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 (@nil Z)) (Z_to_bv 64 0))
  by (intros j Hj; unfold Eb; apply mfE_extra; exact Hj).
pose proof (EXb 0%nat ltac:(unfold A_TEXT; lia)) as E32b.
cbn [Nat.add nth mf_extra map app] in E32b.
pose proof (st_ok_pi_submem Eb _ _ mkb_regions_b HSb
  ltac:(apply submemb_sound; vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HSb1.
clear HSb. mkb_norm HSb1.
pose proof (proj1 CORE2) as HJb.
destruct (cat_row (h_fold vv 24)) as [r|] eqn:ECR.
- (* the row was found: a0 is a row address, the branch is not taken, and MK_CPY answers *)
  assert (Hrlt : (r < pin_spec.CAT_N)%nat) by exact (cat_row_lt _ _ ECR).
  assert (Hptr : 0 < seg_spec.cat_ptr SegInstA.catA (Some r) < 2 ^ 64)
    by (apply cat_ptr_some;
        [ unfold SegInstA.catA; lia
        | unfold SegInstA.catA, pin_spec.CAT_ROW, pin_spec.CAT_N; lia | exact Hrlt ]).
  assert (Hb10 : SegInstA.catA <= bv_unsigned (ew Eb 10) <= SegInstA.catA + 296 * 10).
  { rewrite (EEb 10%nat (10%bv : bv 5) ltac:(vm_compute; reflexivity)), A0. rewrite ?ECR.
    unfold w64. rewrite unsigned_lit_small by lia.
    unfold seg_spec.cat_ptr, pin_spec.CAT_ROW, pin_spec.CAT_N in *. lia. }
  pose proof (st_ok_pi_add_fact Eb _ _ 10%nat (mkAF SegInstA.catA (SegInstA.catA + 296 * 10) 0) HSb1
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; split; [exact Hb10|];
          split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia])) as HSb2.
  clear HSb1. mkb_norm HSb2.
  paj_run_to_sh RUNTOP HSb2 HJb MK_CPY.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
    do 6 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
  pmkst HSb2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq2 := d) in * end.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
  { intros a Ha.
    refine (kept_of_frame Eb _ (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr _ a Ha ltac:(intros [])).
    intros b wlo whi x Hin Hr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia |]).
    destruct Hin. }
  destruct (mf_keep_run0 B v lyc S2 W2 mem2 md2 pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq2
    CX0 CORE2 CELLS2 HJb KEEP0) as (CORE3 & CELLS3 & NPK3 & LOOPK3).
  prreg HSb2 (2%bv : bv 5) P2. prreg HSb2 (3%bv : bv 5) P3. prreg HSb2 (4%bv : bv 5) P4.
  prreg HSb2 (8%bv : bv 5) P8. prreg HSb2 (9%bv : bv 5) P9. prreg HSb2 (18%bv : bv 5) P18.
  prreg HSb2 (19%bv : bv 5) P19. prreg HSb2 (20%bv : bv 5) P20. prreg HSb2 (21%bv : bv 5) P21.
  prreg HSb2 (22%bv : bv 5) P22. prreg HSb2 (24%bv : bv 5) P24. prreg HSb2 (25%bv : bv 5) P25.
  prreg HSb2 (26%bv : bv 5) P26.
  assert (RAT3 : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs2 (ms_regs ms) RAT2);
    [ rewrite P2; apply (EEb 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P3; apply (EEb 3%nat (3%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P4; apply (EEb 4%nat (4%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P8; apply (EEb 8%nat (8%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P9, (EEb 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity)), R2b, R9b; reflexivity
    | rewrite P18, E32b, R18b; reflexivity
    | rewrite P19; apply (EEb 19%nat (19%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P25; apply (EEb 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P26; apply (EEb 26%nat (26%bv : bv 5) ltac:(vm_compute; reflexivity)) ]. }
  unfold mk_mod in HFIN. rewrite ?ECR in HFIN. cbn beta iota in HFIN.
  apply (CPY v lyc S2 W2 (ms_regs ms) (ms_mem ms) mdq2 pos mcc gi line p rest ov vl vv r).
  + unfold mk_base.
    split; [exact CX0|]. split; [exact LS2|]. split; [exact FRM|]. split; [exact CORE3|].
    split; [exact CELLS3|]. split; [exact RAT3|]. split; [exact Hlen|]. split; [exact Hne|].
    split; [exact (LOOPK3 _ _ _ _ _ LOOP2)|]. split; [exact Hovvl|]. split; [exact Hvv|].
    split; [exact (NPK3 _ NP2)|].
    split; [rewrite P24; rewrite (EEb 24%nat (24%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H24'|].
    rewrite P22; rewrite (EEb 22%nat (22%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H22'.
  + exact ECR.
  + exact HFIN.
  + intros i Hi. rewrite KEEP0 by
      (pose proof (hfold_len vv) as Hl; rewrite length_app in Hi; cbn [length] in Hi;
       pose proof (mk_ln_bound (length vv)) as (Hq1 & _); lia).
    exact (HZS2 i Hi).
  + rewrite P20; rewrite (EEb 20%nat (20%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H20'.
  + rewrite P21; rewrite (EEb 21%nat (21%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H21'.
- (* no row: a0 = 0, the branch is taken, and MK_REFUSE answers *)
  assert (A0' : getr regs2 10 = Z_to_bv 64 0)
    by (rewrite A0; rewrite ?ECR; unfold seg_spec.cat_ptr, w64; reflexivity).
  pose proof (st_ok_pi_pin_reg' Eb _ _ (10%bv : bv 5) 0 HSb1 A0' ltac:(vm_compute; reflexivity)) as HSb2.
  clear HSb1. mkb_norm HSb2.
  paj_run_to_sh RUNTOP HSb2 HJb MK_REFUSE.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
    do 6 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
  pmkst HSb2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq2 := d) in * end.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
  { intros a Ha.
    refine (kept_of_frame Eb _ (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr _ a Ha ltac:(intros [])).
    intros b wlo whi x Hin Hr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia |]).
    destruct Hin. }
  destruct (mf_keep_run0 B v lyc S2 W2 mem2 md2 pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq2
    CX0 CORE2 CELLS2 HJb KEEP0) as (CORE3 & CELLS3 & NPK3 & LOOPK3).
  prreg HSb2 (2%bv : bv 5) P2. prreg HSb2 (3%bv : bv 5) P3. prreg HSb2 (4%bv : bv 5) P4.
  prreg HSb2 (8%bv : bv 5) P8. prreg HSb2 (9%bv : bv 5) P9. prreg HSb2 (18%bv : bv 5) P18.
  prreg HSb2 (19%bv : bv 5) P19. prreg HSb2 (22%bv : bv 5) P22. prreg HSb2 (24%bv : bv 5) P24.
  prreg HSb2 (25%bv : bv 5) P25. prreg HSb2 (26%bv : bv 5) P26.
  assert (RAT3 : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs2 (ms_regs ms) RAT2);
    [ rewrite P2; apply (EEb 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P3; apply (EEb 3%nat (3%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P4; apply (EEb 4%nat (4%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P8; apply (EEb 8%nat (8%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P9, (EEb 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity)), R2b, R9b; reflexivity
    | rewrite P18, E32b, R18b; reflexivity
    | rewrite P19; apply (EEb 19%nat (19%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P25; apply (EEb 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity))
    | rewrite P26; apply (EEb 26%nat (26%bv : bv 5) ltac:(vm_compute; reflexivity)) ]. }
  unfold mk_mod in HFIN. rewrite ?ECR in HFIN. cbn beta iota in HFIN.
  apply (REF v lyc S2 W2 (ms_regs ms) (ms_mem ms) mdq2 pos mcc gi line p rest ov vl vv).
  + unfold mk_base.
    split; [exact CX0|]. split; [exact LS2|]. split; [exact FRM|]. split; [exact CORE3|].
    split; [exact CELLS3|]. split; [exact RAT3|]. split; [exact Hlen|]. split; [exact Hne|].
    split; [exact (LOOPK3 _ _ _ _ _ LOOP2)|]. split; [exact Hovvl|]. split; [exact Hvv|].
    split; [exact (NPK3 _ NP2)|].
    split; [rewrite P24; rewrite (EEb 24%nat (24%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H24'|].
    rewrite P22; rewrite (EEb 22%nat (22%bv : bv 5) ltac:(vm_compute; reflexivity)); exact H22'.
  + exact HFIN.
Qed.

About mk_fexit_ok.
Print Assumptions mk_fexit_ok.
End e.
End f.
End d.
