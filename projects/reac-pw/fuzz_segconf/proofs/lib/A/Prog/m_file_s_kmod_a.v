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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 433 of its 486 lines of code are new or changed and 400 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A): the first piece of segment S_MF_KMOD of m_file's walk (the G2 walk owner's
   guide/MF-CUTS-A.md section 4), from the cut KMODEL 0x867b8 to KIGN 0x8693c, MK_FOLD 0x867f8 or MK_FEXIT 0x86864
   (lib/A/Prog/m_file_s_kmod_m.v). The KMOD ieq sub-lane of the G2 walk owner's G2 (parent the KMOD segment lane).
   proves no function (kind: segment lemma of m_file's walk: KMODEL 0x867b8 to KIGN / MK_FOLD / MK_FEXIT inside
   S_MF_KMOD).

   mk_kmodel_ok : forall n, MF_KIGN_stmt B n -> MK_FOLD_stmt B n -> MK_FEXIT_stmt B n -> MF_KMODEL_stmt B n.

   The code (listing m_file.fuzz_segconf.asan.s lines 577-592):
     867b8 auipc a0 / 867bc addi a2,a0,-1432   a2 = 0x21220 "model" (listing object 19)
     867c0 mv a0,s11 / 867c4 mv a1,s6          a0 = k = p + ok, a1 = kl
     867c8 jal ieq                             a0 = b2z (ieq k "model") (ieq_contract)
     867cc beqz a0,8693c                       0: KIGN, with "model" added to the words missed
     867d0 li a0,23 / 867d4 bltu s4,a0 / 867d8 li s4,23     s4 = mk_ln vl = min(vl, 23)
     867dc mv s6,s8 / 867e0 ld s8,104(s1)      s6 = line + 1, s8 = FAKE
     867e4 beq s7,s5,86864                     vl = 0: MK_FEXIT (h_fold [] 24 = [])
     867e8 mv a0,s5 / 867ec ld a1,152(s1) / 867f0 mv a2,a1 / 867f4 mv a3,s4   MK_FOLD with i = 0
   The model: with ieq k "role" = false (the K cut's missed list) and ieq k "model" = true, mk_disp is mk_mod
   (m_file_s_kmod_m.v mk_disp_model).

   How: the piece stores no byte, so its symbolic state is m_file_sd.v's mf_seed (cells, np, low.i in scope) with
   the slot window closed (mka_seed, check_reply_s7.v cr7_seed's form); every run then keeps the reader everywhere
   (mka_frame_all) and m_file_k.v's mf_carry_eq carries the cut facts. The run 0x867b8-0x867c4 stops at the jal;
   ieq is the shared step m_file_iq.v mf_ieq_call (the key as seg_spec.zb k at p + ok, in the text's block; the
   word S_model at listing object 19, m_file_sd.v mf_lit_obj); at the return 0x867cc (mka_after) a0 is pinned to
   0 or 1, the bltu and beq are split on their conditions (mka_bt_ltu, mka_bt_eq), and mka_to_ign / mka_to_fold /
   mka_to_fexit close with the three cut statements. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import ieq_c m_file_c m_file_m m_file_s_kmod_m
  m_file_s_kign_t m_file_s_kmod_t m_file_sd m_file_k m_file_iq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the model side ===================================== *)
(* the words missed at KIGN: "role" (the K cut's) and "model" (ieq's 0) *)
Lemma mka_missed : forall k, Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = false ->
Forall (fun w => ieq k w = false) [S_role; S_model].
Proof.
intros k H1 H2. inversion H1 as [|w l Hr _ E]; subst. constructor; [exact Hr|]. constructor; [exact H2 | constructor].
Qed.
Lemma mka_role : forall k, Forall (fun w => ieq k w = false) [S_role] -> ieq k S_role = false.
Proof. intros k H. inversion H; assumption. Qed.
(* the model branch: ieq k "model" = true turns the K cut's mk_disp into mk_mod *)
Lemma mka_fin_model : forall mcc gi k vv line rest fin,
Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = true ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = fin ->
mf_fin (mk_mod mcc gi vv (line + 1), Some gi) line rest = fin.
Proof. intros mcc gi k vv line rest fin HM HT H. rewrite <- (mk_disp_model mcc gi k vv (line + 1) (mka_role k HM) HT). exact H. Qed.
Lemma mka_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
intros rest. unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst length] in *. lia.
Qed.

(* ============================ the key's bytes and the ieq premises ============================ *)
(* a part of an addressable range is addressable *)
Lemma mka_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
sa_addr rd q' n'.
Proof.
intros rd q n q' n' (H0 & H63 & HR & HA & HV) Hq Hn' Hle.
split; [lia|]. split; [lia|]. split.
{ unfold amem_range in *. lia. }
split; [exact (range_addressable_sub rd SHADOW_OFF q n q' n' HA Hq Hle)|].
intros Hp s Hs. apply (HV ltac:(lia)). unfold shadow_addr in *. split.
- pose proof (Z.div_le_mono q q' 8 ltac:(lia) Hq).
  pose proof (Z.div_le_mono (SHADOW_OFF + q / 8) (SHADOW_OFF + q' / 8) 8 ltac:(lia) ltac:(lia)). lia.
- pose proof (Z.div_le_mono (q' + n' - 1) (q + n - 1) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (SHADOW_OFF + (q' + n' - 1) / 8) (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* 0x867cc, ieq's return point in the piece (listing offset AF_m_file + 0x910) *)
Definition MKA_RET : Z := AF_m_file + 0x910.
(* the piece's regions: m_file_sd.v's mf_regions (cells, np, low.i in scope) with the slot window closed *)
Definition mka_rs : smem :=
  list_upd (mf_regions true true [] false false [] false MF_LOW_ON) 1 (set_window (mf_r_slots true true []) 0 0).
Definition mka_ss (pc : Z) : sstate := mkSS pc sr_mf mka_rs None mf_facts.

(* the two data branches of the piece (bltu 0x867d4, beq 0x867e4) on atoms of known value *)
Lemma mka_bt_ltu : forall E (i : nat) z x, ew E i = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff i 0)) (sv_denot E (SLit z)) = (x <? z).
Proof.
intros E i z x H Hx Hz. cbn [branch_taken sv_denot]. rewrite bv_ltu_unsigned, H.
rewrite (unsigned_lit_small x) by lia. rewrite Z.add_0_r, !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma mka_bt_eq : forall E (i j : nat) x y, ew E i = Z_to_bv 64 x -> ew E j = Z_to_bv 64 y ->
0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff i 0)) (sv_denot E (SOff j 0)) = (x =? y).
Proof.
intros E i j x y Hi Hj Hx Hy. cbn [branch_taken sv_denot]. rewrite bv_eqb_unsigned, Hi, Hj.
rewrite (unsigned_lit_small x), (unsigned_lit_small y) by lia. rewrite !Z.add_0_r, !unsigned_lit_small by lia.
reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.

(* the text's bytes [p + ok, p + ok + kl) lie in the text's heap block at every state of the walk *)
Lemma mka_key_heap : forall v lyc Sc Wc memc mdc pos lowsh mcc Wq memq cur line p rest ok kl ov vl k vv,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mf_loop v Wq memq mcc cur line p rest -> mk_kv rest ok kl ov vl k vv ->
sa_heap B lyc Sc (p + Z.of_nat ok) (Z.of_nat kl).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc Wq memq cur line p rest ok kl ov vl k vv CX CORE LOOP (Hk & _).
pose proof (mka_line_len rest) as Hll.
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (b & m & Hin & Hb & Hm).
destruct LOOP as (Hlr & _ & Ep & _).
exists b, m. split; [exact Hin|]. subst p. lia.
Qed.
(* ieq's premises on the key at the call (mf_ieq_call's s, l, n): k = the bytes [ok, ok + kl) of the text left,
   as list byte through the reader (ki_zs_slice, ki_bytes_of_zs), addressable, in the text's heap block *)
Lemma mka_key_pre : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest ok kl ov vl k vv,
mf_cx B v -> mf_ls v lyc Sc -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mf_loop v Wc memc mcc cur line p rest -> mk_kv rest ok kl ov vl k vv ->
p + Z.of_nat ok <> 0 /\ sa_bytes (rdW Wc memc) (p + Z.of_nat ok) (seg_spec.zb k) /\
Z.of_nat (length (seg_spec.zb k)) = Z.of_nat kl /\ sa_addr (rdW Wc memc) (p + Z.of_nat ok) (Z.of_nat kl) /\
sa_heap B lyc Sc (p + Z.of_nat ok) (Z.of_nat kl) /\ seg_spec.zs (seg_spec.zb k) = k.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest ok kl ov vl k vv CX LS CORE LOOP KV.
pose proof (mka_key_heap v lyc Sc Wc memc mdc pos lowsh mcc Wc memc cur line p rest ok kl ov vl k vv CX CORE LOOP KV)
  as HH.
pose proof (mka_line_len rest) as Hll.
pose proof KV as (Hk & _ & Ek & _).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _).
pose proof LOOP as (Hlr & _ & Ep & ((HZ & _) & _) & HADDR & _).
assert (HZr : sa_zs (rdW Wc memc) p rest).
{ intros i Hi. rewrite <- (app_nth1 rest [0] 0 Hi). apply HZ. rewrite length_app. cbn [length]. lia. }
pose proof (ki_zs_slice (rdW Wc memc) p rest ok kl HZr ltac:(lia)) as HS. rewrite Ek in HS.
destruct (ki_bytes_of_zs SEGS (w_H Wc) memc (p + Z.of_nat ok) k HS) as (HB & HZk & _).
assert (Hlen : length k = kl) by (rewrite <- Ek, length_firstn, length_skipn; lia).
split; [subst p; lia|]. split; [exact HB|].
split; [unfold seg_spec.zb; rewrite length_map, Hlen; reflexivity|].
split; [apply (mka_sa_addr_sub _ p (Z.of_nat (length rest) + 1)); [exact HADDR | lia | lia | lia]|].
split; [exact HH | exact HZk].
Qed.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the piece's symbolic state: mf_seed's (cells, np in 144(s1), low.i in scope, no extra atom) with the slot
   window closed (check_reply_s7.v cr7_seed's form): the piece stores no byte, so every region is read-only *)
Lemma mka_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest -> mf_np v memc Wc (mf_next p rest) ->
st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) (mka_ss pc)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest pc CX CORE CELLS RA LOOP NP.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) (mf_next p rest) [] pc
  true true [] false false [] false CX CORE (mf_regs_base_of B v lyc pos regs1 RA) (fun _ => CELLS)
  (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) CX CORE (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 LOOP)))))))
  (fun _ => NP) (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS.
pose proof (st_ok_pi_region_nth _ _ _ 1 (mf_r_slots true true []) HS eq_refl) as Hr.
exact (ast_ok_pi_set_region _ _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 0 0) HS eq_refl
  eq_refl ltac:(vm_compute; reflexivity) (region_ok_rewindow SEGS _ _ _ 0 0 Hr ltac:(intros o Ho; lia))).
Qed.

(* a run from a state whose regions are all read-only changes no byte *)
Lemma mka_frame_all : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF HRO a _. apply (aview_eq_of SEGS). apply HF. intros (r & Hin & Hr).
rewrite Forall_forall in HRO. pose proof (HRO r Hin). lia.
Qed.

(* every region of the piece's state is read-only: the run's awr_ok *)
Ltac mka_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* after a run: the cut facts at the run's memory (mf_carry_eq) *)
Ltac mka_carry CX CORE LOOP CELLS NP CORE' LOOP' CELLS' NP' :=
  lazymatch goal with
  | HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq ?mdq _,
    HFr : frame_of _ ?rsx (mrestrict _ _) (mrestrict _ _) |- _ =>
    let K0 := fresh "K0" in
    pose proof (mka_frame_all _ _ _ _ _ HFr ltac:(cbn [ss_mem]; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil))
      as K0;
    let KC := fresh "KC" in let KN := fresh "KN" in
    destruct (mf_carry_eq B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX CORE HJ K0 LOOP) as (CORE' & LOOP' & KC & KN);
    pose proof (KC _ CELLS) as CELLS'; pose proof (KN _ NP) as NP'; clear KC KN K0
  end.


(* the three ends of the piece, from the plain facts at the state the run reaches *)
Lemma mka_to_ign : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
MF_KIGN_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = false ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
getr regs1 27 = w64 (p + Z.of_nat ok) -> getr regs1 22 = w64 (Z.of_nat kl) ->
getr regs1 21 = w64 (p + Z.of_nat ov) -> getr regs1 20 = w64 (Z.of_nat vl) ->
getr regs1 23 = w64 (p + Z.of_nat (ov + vl)) -> getr regs1 24 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
mf_at B v Wc regs1 memc mdc MF_KIGN.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv KIGN CX LS FRM CORE CELLS RA LEN NE
  LOOP KV MISS HM FIN R27 R22 R21 R20 R23 R24 NP.
exact (KIGN v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE CELLS RA LEN NE LOOP KV
  (mka_missed k MISS HM) FIN R27 R22 R21 R20 R23 R24 NP).
Qed.

Lemma mka_to_fold : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z),
MK_FOLD_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = true ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_np v memc Wc (mf_next p rest) -> (0 < vl)%nat ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln vl)) ->
getr regs1 21 = w64 (p + Z.of_nat ov) -> getr regs1 10 = w64 (p + Z.of_nat ov) ->
getr regs1 11 = w64 (frame_addr lyc 1 pos + 32) -> getr regs1 12 = w64 (frame_addr lyc 1 pos + 32) ->
getr regs1 13 = w64 (Z.of_nat (mk_ln vl)) ->
mf_at B v Wc regs1 memc mdc MK_FOLD.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv FOLD CX LS FRM CORE CELLS RA LEN NE
  LOOP KV MISS HM FIN NP Hvl R24 R22 R20 R21 R10 R11 R12 R13.
destruct KV as (Hk & Hv & Ek & Ev).
apply (FOLD v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv 0%nat).
- unfold mk_base. repeat (split; [eassumption|]). eassumption.
- exact (mka_fin_model mcc gi k vv line rest _ MISS HM FIN).
- exact (proj2 (proj2 (mk_ln_bound vl)) Hvl).
- intros i Hi. cbn [firstn map length] in Hi. exfalso. exact (Nat.nlt_0_r i Hi).
- exact R20.
- rewrite Nat.add_0_r. exact R21.
- rewrite Nat.add_0_r. exact R10.
- replace (frame_addr lyc 1 pos + 32 + Z.of_nat 0) with (frame_addr lyc 1 pos + 32) by lia. exact R11.
- replace (frame_addr lyc 1 pos + 32 + Z.of_nat 0) with (frame_addr lyc 1 pos + 32) by lia. exact R12.
- rewrite Nat.sub_0_r. exact R13.
Qed.

Lemma mka_to_fexit : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov : nat) (k vv : list Z),
MK_FEXIT_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs1 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov 0 k vv -> Forall (fun w => ieq k w = false) [S_role] -> ieq k S_model = true ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
mf_np v memc Wc (mf_next p rest) ->
getr regs1 24 = w64 (frame_addr lyc 1 pos) -> getr regs1 22 = w64 (line + 1) ->
getr regs1 20 = w64 (Z.of_nat (mk_ln 0)) ->
mf_at B v Wc regs1 memc mdc MK_FEXIT.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov k vv FEXIT CX LS FRM CORE CELLS RA LEN NE
  LOOP KV MISS HM FIN NP R24 R22 R20.
destruct KV as (Hk & Hv & Ek & Ev).
apply (FEXIT v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov 0%nat vv).
- unfold mk_base. repeat (split; [eassumption|]). eassumption.
- exact (mka_fin_model mcc gi k vv line rest _ MISS HM FIN).
- intros i Hi. rewrite <- Ev in Hi. unfold h_fold in Hi. cbn [firstn] in Hi. rewrite firstn_nil in Hi.
  cbn [map length] in Hi. exfalso. exact (Nat.nlt_0_r i Hi).
- exact R20.
Qed.

(* the frame's address is a mapped, low address *)
Lemma mka_fb : forall v lyc Sc Wc memc mdc pos lowsh mcc, mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= 2 ^ 47.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CORE.
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((C1 & C2) & _). unfold YG0f.ASAN_CEIL in C1, C2.
unfold in_app, kLowShadowBeg, kHighMemBeg in F3. lia.
Qed.

(* the registers of the piece's state that are their own atoms: unchanged by a run that does not write them *)
Ltac mka_kept HS HAE l KEEP :=
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ l HS HAE ltac:(vm_compute; reflexivity)) as KEEP;
  cbn [ms_regs restrict] in KEEP.
(* name the stop's pc by its cut *)
Ltac mka_pc P := lazymatch goal with |- context [Z_to_bv 64 (BASE + ?x)] => change (BASE + x) with (BASE + P) end.
(* the registers every cut names (mf_regs_at) at the state a run reaches *)
Ltac mka_ra HS HAE E2 E32 RA RA2 RA9 RA18 RA1 :=
  let KB := fresh "KB" in let Q9 := fresh "Q9" in let Q18 := fresh "Q18" in
  mka_kept HS HAE ([2%bv; 3%bv; 4%bv; 8%bv; 19%bv; 25%bv; 26%bv] : list (bv 5)) KB;
  prreg HS (9%bv : bv 5) Q9; prreg HS (18%bv : bv 5) Q18; rewrite E2 in Q9; rewrite E32 in Q18;
  pose proof (mf_regs_at_of B _ _ _ _ _ RA (KB 2%bv ltac:(cbn; tauto)) (KB 3%bv ltac:(cbn; tauto))
    (KB 4%bv ltac:(cbn; tauto)) (KB 8%bv ltac:(cbn; tauto)) ltac:(rewrite Q9, RA9, RA2; reflexivity)
    ltac:(rewrite Q18, RA18; reflexivity) (KB 19%bv ltac:(cbn; tauto)) (KB 25%bv ltac:(cbn; tauto))
    (KB 26%bv ltac:(cbn; tauto))) as RA1;
  clear KB Q9 Q18.

(* 0x867cc .. KIGN / MK_FOLD / MK_FEXIT: the branch on ieq's answer, ln = min(vl, 23), s6 = line + 1, s8 = FAKE,
   the empty-value test, the fold's registers *)
Lemma mka_after : forall n, MF_KIGN_stmt B n -> MK_FOLD_stmt B n -> MK_FEXIT_stmt B n ->
forall v lyc Sc Wc regs2 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
mf_regs_at B v lyc pos regs2 ->
(length rest <= n)%nat -> rest <> [] -> mf_loop v Wc memc mcc (Some gi) line p rest ->
mk_kv rest ok kl ov vl k vv -> Forall (fun w => ieq k w = false) [S_role] ->
mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v ->
getr regs2 27 = w64 (p + Z.of_nat ok) -> getr regs2 22 = w64 (Z.of_nat kl) ->
getr regs2 21 = w64 (p + Z.of_nat ov) -> getr regs2 20 = w64 (Z.of_nat vl) ->
getr regs2 23 = w64 (p + Z.of_nat (ov + vl)) -> getr regs2 24 = w64 (line + 1) ->
mf_np v memc Wc (mf_next p rest) ->
getr regs2 10 = w64 (seg_spec.b2z (ieq k S_model)) ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + MKA_RET)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros n KIGN FOLD FEXIT v lyc Sc Wc regs2 memc mdc pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE CELLS RA
  LEN NE LOOP KV MISS FIN R27 R22 R21 R20 R23 R24 NP R10.
pose proof (mka_seed v lyc Sc Wc regs2 memc mdc pos mcc gi line p rest MKA_RET CX CORE CELLS RA LOOP NP) as HS.
set (E := mfE regs2 v lyc pos (Some gi) (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 (mf_extra v lyc pos (Some gi) (mf_next p rest) [])) E)
  by (split; [intros nn Hn; unfold E; apply mfE_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = getr regs2 2) by (unfold E; apply mfE_reg; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E; exact (mfE_extra regs2 v lyc pos _ _ [] 0 ltac:(unfold A_TEXT; lia))).
assert (ER20 : ew E 20 = Z_to_bv 64 (Z.of_nat vl)) by (unfold E; rewrite (mfE_reg _ _ _ _ _ _ _ 20 20%bv eq_refl); exact R20).
assert (ER21 : ew E 21 = Z_to_bv 64 (p + Z.of_nat ov))
  by (unfold E; rewrite (mfE_reg _ _ _ _ _ _ _ 21 21%bv eq_refl); exact R21).
assert (ER23 : ew E 23 = Z_to_bv 64 (p + Z.of_nat (ov + vl)))
  by (unfold E; rewrite (mfE_reg _ _ _ _ _ _ _ 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = getr regs2 24) by (unfold E; apply mfE_reg; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 (frame_addr lyc 1 pos))
  by (unfold E; exact (mfE_extra regs2 v lyc pos _ _ [] 2 ltac:(unfold A_TEXT; lia))).
pose proof LOOP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _).
pose proof (mka_line_len rest) as Hll. pose proof KV as (Hk & Hv & _).
destruct (mka_fb v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CORE) as (Hfb1 & Hfb2).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
pose proof CORE as (HJ & _).
pose proof RA as (RA2 & RA3 & RA4 & RA8 & RA9 & RA18 & RA19 & RA25 & RA26).
destruct (ieq k S_model) eqn:HM; cbn [seg_spec.b2z] in R10.
- (* ieq "model" = 1 *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS ltac:(exact R10) eq_refl) as HSp.
  lazymatch type of HSp with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HSp end.
  clear HS. rename HSp into HS.
  paj_run_tok RUN HS HJ SHOK Bspan; [mka_awr|].
  mka_carry CX CORE LOOP CELLS NP CORE1 LOOP1 CELLS1 NP1.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* bltu s4, 23 taken: vl < 23, s4 stays vl *)
    rewrite (mka_bt_ltu E 20 23 (Z.of_nat vl) ER20 ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_lt in Hc.
    assert (Hln : Z.of_nat (mk_ln vl) = Z.of_nat vl) by (unfold mk_ln; lia).
    paj_run_tok RUN HS HJ SHOK Bspan; [mka_awr|].
    mka_carry CX CORE1 LOOP1 CELLS1 NP1 CORE2 LOOP2 CELLS2 NP2.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* beq s7, s5 taken: vl = 0, MK_FEXIT *)
      rename Hc0 into Hq.
      rewrite (mka_bt_eq E 23 21 _ _ ER23 ER21 ltac:(lia) ltac:(lia)) in Hq. apply Z.eqb_eq in Hq.
      assert (Hv0 : vl = 0%nat) by lia. subst vl.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_FEXIT; [mka_awr|].
      mka_carry CX CORE2 LOOP2 CELLS2 NP2 CORE3 LOOP3 CELLS3 NP3.
      mka_ra HS HAE E2 E32 RA RA2 RA9 RA18 RA1.
      prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
      pmkst HS.
      mka_pc MK_FEXIT.
      exact (mka_to_fexit n v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov k vv FEXIT CX LS FRM CORE3 CELLS3 RA1
        LEN NE LOOP3 KV MISS HM FIN NP3 ltac:(rewrite Q24, E34; reflexivity) ltac:(rewrite Q22, E24; exact R24)
        ltac:(rewrite Q20, ER20; reflexivity)).
    * (* beq not taken: vl > 0, MK_FOLD at i = 0 *)
      rename Hc0 into Hq.
      rewrite (mka_bt_eq E 23 21 _ _ ER23 ER21 ltac:(lia) ltac:(lia)) in Hq. apply Z.eqb_neq in Hq.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_FOLD; [mka_awr|].
      mka_carry CX CORE2 LOOP2 CELLS2 NP2 CORE3 LOOP3 CELLS3 NP3.
      mka_ra HS HAE E2 E32 RA RA2 RA9 RA18 RA1.
      prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
      prreg HS (13%bv : bv 5) Q13. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
      pmkst HS.
      mka_pc MK_FOLD.
      exact (mka_to_fold n v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv FOLD CX LS FRM CORE3 CELLS3 RA1
        LEN NE LOOP3 KV MISS HM FIN NP3 ltac:(lia) ltac:(rewrite Q24, E34; reflexivity)
        ltac:(rewrite Q22, E24; exact R24) ltac:(rewrite Q20, ER20, Hln; reflexivity)
        ltac:(rewrite Q21, ER21; reflexivity) ltac:(rewrite Q10, ER21; reflexivity)
        ltac:(rewrite Q11, E34, unsigned_lit_small by lia; reflexivity)
        ltac:(rewrite Q12, E34, unsigned_lit_small by lia; reflexivity)
        ltac:(rewrite Q13, ER20, Hln; reflexivity)).
  + (* bltu not taken: vl >= 23, s4 = 23 *)
    rewrite (mka_bt_ltu E 20 23 (Z.of_nat vl) ER20 ltac:(lia) ltac:(lia)) in Hc.
    apply Z.ltb_ge in Hc.
    assert (Hln : Z.of_nat (mk_ln vl) = 23) by (unfold mk_ln; lia).
    paj_run_tok RUN HS HJ SHOK Bspan; [mka_awr|].
    mka_carry CX CORE1 LOOP1 CELLS1 NP1 CORE2 LOOP2 CELLS2 NP2.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* beq taken would need vl = 0 *)
      rename Hc0 into Hq.
      rewrite (mka_bt_eq E 23 21 _ _ ER23 ER21 ltac:(lia) ltac:(lia)) in Hq. apply Z.eqb_eq in Hq. exfalso. lia.
    * rename Hc0 into Hq.
      rewrite (mka_bt_eq E 23 21 _ _ ER23 ER21 ltac:(lia) ltac:(lia)) in Hq. apply Z.eqb_neq in Hq.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_FOLD; [mka_awr|].
      mka_carry CX CORE2 LOOP2 CELLS2 NP2 CORE3 LOOP3 CELLS3 NP3.
      mka_ra HS HAE E2 E32 RA RA2 RA9 RA18 RA1.
      prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
      prreg HS (13%bv : bv 5) Q13. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
      prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
      pmkst HS.
      mka_pc MK_FOLD.
      exact (mka_to_fold n v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv FOLD CX LS FRM CORE3 CELLS3 RA1
        LEN NE LOOP3 KV MISS HM FIN NP3 ltac:(lia) ltac:(rewrite Q24, E34; reflexivity)
        ltac:(rewrite Q22, E24; exact R24) ltac:(rewrite Q20, Hln; reflexivity)
        ltac:(rewrite Q21, ER21; reflexivity) ltac:(rewrite Q10, ER21; reflexivity)
        ltac:(rewrite Q11, E34, unsigned_lit_small by lia; reflexivity)
        ltac:(rewrite Q12, E34, unsigned_lit_small by lia; reflexivity)
        ltac:(rewrite Q13, Hln; reflexivity)).
- (* ieq "model" = 0: beqz to KIGN *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS ltac:(exact R10) eq_refl) as HSp.
  lazymatch type of HSp with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HSp end.
  clear HS. rename HSp into HS.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KIGN; [mka_awr|].
  mka_carry CX CORE LOOP CELLS NP CORE1 LOOP1 CELLS1 NP1.
  mka_kept HS HAE ([2%bv; 3%bv; 4%bv; 8%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] : list (bv 5)) KEEP.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  rewrite E2 in Q9. rewrite E32 in Q18.
  pose proof (mf_regs_at_of B v lyc pos regs2 _ RA (KEEP 2%bv ltac:(cbn; tauto)) (KEEP 3%bv ltac:(cbn; tauto))
    (KEEP 4%bv ltac:(cbn; tauto)) (KEEP 8%bv ltac:(cbn; tauto)) ltac:(rewrite Q9, RA9, RA2; reflexivity)
    ltac:(rewrite Q18, RA18; reflexivity) (KEEP 19%bv ltac:(cbn; tauto)) (KEEP 25%bv ltac:(cbn; tauto))
    (KEEP 26%bv ltac:(cbn; tauto))) as RA1.
  pmkst HS.
  mka_pc MF_KIGN.
  exact (mka_to_ign n v lyc Sc Wc _ _ _ pos mcc gi line p rest ok kl ov vl k vv KIGN CX LS FRM CORE1 CELLS1 RA1 LEN NE
    LOOP1 KV MISS HM FIN
    ltac:(rewrite (KEEP 27%bv ltac:(cbn; tauto)); exact R27) ltac:(rewrite (KEEP 22%bv ltac:(cbn; tauto)); exact R22)
    ltac:(rewrite (KEEP 21%bv ltac:(cbn; tauto)); exact R21) ltac:(rewrite (KEEP 20%bv ltac:(cbn; tauto)); exact R20)
    ltac:(rewrite (KEEP 23%bv ltac:(cbn; tauto)); exact R23) ltac:(rewrite (KEEP 24%bv ltac:(cbn; tauto)); exact R24)
    NP1).
Qed.

(* the shared Section hypotheses this piece uses (CALLS-CONTEXT.md; the m_file cut-statement lane's list): the call target of ieq,
   the read-only range for ieq's arodata_okP (m_file_k.v mf_rod_now), and ieq's contract at every FP state *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.

(* a callee-saved register at the run's stop equals its value at the run's start: both are the same symbolic value
   (check_reply_s2.v cr2_reg_eq / cr2_regs_pres) *)
Ltac mka_reg_eq HS0 HS :=
  lazymatch goal with |- getr _ ?r = getr _ ?r =>
  lazymatch type of HS with st_ok ?sg ?Ev ?ss (restrict ?H ?ms) =>
  lazymatch type of HS0 with st_ok_pi _ _ ?Ev0 ?ss0 (restrict ?H0 ?ms0) =>
  transitivity (sv_denot Ev (sr_get (ss_regs ss) r)); [exact (st_ok_restrict_reg sg H Ev ss ms r HS)|];
  etransitivity; [| symmetry; exact (st_ok_pi_restrict_reg H0 Ev0 ss0 ms0 r HS0)];
  f_equal; vm_compute; reflexivity end end end.
Ltac mka_regs_pres HS0 HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [-> | Hc]; [mka_reg_eq HS0 HS |]); subst r; mka_reg_eq HS0 HS.
Ltac mka_preg HP r R := etransitivity; [exact (HP r ltac:(unfold acallee_saved; lia)) | exact R].

(* KMODEL 0x867b8: a2 = "model", a0 = k, a1 = kl, ieq; then mka_after at its return 0x867cc *)
Theorem mk_kmodel_ok : forall n, MF_KIGN_stmt B n -> MK_FOLD_stmt B n -> MK_FEXIT_stmt B n -> MF_KMODEL_stmt B n.
Proof.
intros n KIGN FOLD FEXIT.
unfold MF_KMODEL_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv CX LS FRM CORE CELLS RA LEN NE LOOP KV MISS FIN
  R27 R22 R21 R20 R23 R24 NP.
unfold mf_at.
pose proof (mka_seed v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest MF_KMODEL CX CORE CELLS RA LOOP NP) as HS.
set (E := mfE regs1 v lyc pos (Some gi) (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
assert (E27 : ew E 27 = getr regs1 27) by (unfold E; apply mfE_reg; reflexivity).
assert (E22 : ew E 22 = getr regs1 22) by (unfold E; apply mfE_reg; reflexivity).
assert (EO19 : ew E (A_OBJ 19) = Z_to_bv 64 (VAL (A_OBJ 19)))
  by (unfold E; apply mfE_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof CORE as (HJ & _).
pose proof HS as HS0.
paj_run_tok RUN HS HJ SHOK Bspan; [mka_awr|].
mka_carry CX CORE LOOP CELLS NP CORE1 LOOP1 CELLS1 NP1.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) => set (rc1 := ms_regs msc) in * end.
assert (HPc : aregs_preserved regs1 rc1) by (unfold rc1; mka_regs_pres HS0 HS).
pose proof (mf_regs_at_of B v lyc pos regs1 rc1 RA (HPc 2 ltac:(unfold acallee_saved; lia))
  (HPc 3 ltac:(unfold acallee_saved; lia)) (HPc 4 ltac:(unfold acallee_saved; lia))
  (HPc 8 ltac:(unfold acallee_saved; lia)) (HPc 9 ltac:(unfold acallee_saved; lia))
  (HPc 18 ltac:(unfold acallee_saved; lia)) (HPc 19 ltac:(unfold acallee_saved; lia))
  (HPc 25 ltac:(unfold acallee_saved; lia)) (HPc 26 ltac:(unfold acallee_saved; lia))) as RAc.
pose proof RAc as (RC2 & RC3 & RC4 & RC8 & _).
pmkst HS.
assert (SIG_IEQ : SIGMA SS_ieq = BASE + AF_ieq)
  by (rewrite (SIGP SS_ieq) by (unfold seg_prog_syms; repeat (first [left; reflexivity | right])); reflexivity).
rewrite SIG_IEQ.
destruct (mka_key_pre v lyc Sc Wc _ _ pos MF_LOW_ON mcc (Some gi) line p rest ok kl ov vl k vv CX LS CORE1 LOOP1 KV)
  as (Hs0 & HSB & HLEN & HSA & HSH & HZk).
apply (mf_ieq_call B RELRO IEQ v lyc Sc Wc rc1 _ _ pos MF_LOW_ON mcc (Some gi) line p rest (mf_next p rest)
  MKA_RET (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k) S_model CX LS CORE1 CELLS1 LOOP1 NP1 RC2 RC3 RC4 RC8).
- exact Q1.
- unfold MKA_RET, AF_m_file. lia.
- reflexivity.
- unfold M_FILE_LITS. repeat (first [left; reflexivity | right]).
- rewrite Q10, E27. exact R27.
- rewrite Q11, E22. exact R22.
- rewrite Q12. change (ew E 260) with (ew E (A_OBJ 19)).
  rewrite EO19, (mf_lit_obj VOBJS S_model 19 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity.
- exact Hs0.
- exact HSB.
- exact HLEN.
- exact HSA.
- exact HSH.
- intros S2 W2 regs2 mem2 md2 HW LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A0 K2.
  rewrite HZk in A0.
  pose proof (aregs_preserved_trans _ _ _ HPc HP2) as HPa.
  pose proof (mf_regs_at_of B v lyc pos regs1 regs2 RA (HPa 2 ltac:(unfold acallee_saved; lia))
    (HPa 3 ltac:(unfold acallee_saved; lia)) (HPa 4 ltac:(unfold acallee_saved; lia))
    (HPa 8 ltac:(unfold acallee_saved; lia)) (HPa 9 ltac:(unfold acallee_saved; lia))
    (HPa 18 ltac:(unfold acallee_saved; lia)) (HPa 19 ltac:(unfold acallee_saved; lia))
    (HPa 25 ltac:(unfold acallee_saved; lia)) (HPa 26 ltac:(unfold acallee_saved; lia))) as RA2.
  exact (mka_after n KIGN FOLD FEXIT v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv CX LS2 FRM
    CORE2 CELLS2 RA2 LEN NE LOOP2 KV MISS FIN ltac:(mka_preg HPa 27 R27) ltac:(mka_preg HPa 22 R22)
    ltac:(mka_preg HPa 21 R21) ltac:(mka_preg HPa 20 R20) ltac:(mka_preg HPa 23 R23) ltac:(mka_preg HPa 24 R24)
    NP2 A0).
Qed.
(* inside the Sections: the piece's hypotheses as its assumptions *)
Print Assumptions mk_kmodel_ok.
End e.
End f.
End d.
About mk_kmodel_ok.
Print Assumptions mk_kmodel_ok.
