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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 642 of its 693 lines of code are new or changed and 402 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the kit of the
   BAD piece of segment B10b of reac_segconf_parse_file's walk (pf_seg_B10b_k.v PB10_R: HA_JOIN n -> H_BAD n,
   BAD 0x88960 -> the refuse call 0x88978 -> JOIN 0x88dc8). The B10b segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: call-site and state-transport lemmas of a segment piece).
   ADAPTED from a working branch's lib/A/Prog/pf_a6_k.v (a6_keeps / a6_keeps_call / a6_keeps_refuse /
   a6_base_move / a6_buf_arg), a working branch's lib/A/Prog/pf_a7_s.v (a7_refuse_site_ok, a7_apart,
   a7_va_ok), a working branch's lib/A/Prog/pf_a10b_b3.v (b_refuse_pre, b3_cn_arg, b3_nm_str) and this
   lane's image-B files pf_seg_B10b_j.v (b10j_geo) and the image-B G3 walk owner's B11c kit lib/B/Prog/pf_seg_B11c_k.v
   (b11_geo / b11_addr_frame / b11_fframe / b11_va_frame / b11_chain), re-derived on image B: B's real frame is
   352 bytes (s1 = (sp0 - 0x160) & -32, s1 in [sp0 - 368, sp0 - 352]), STK_reac_segconf_parse_file = 12832, c
   lives only in slot 0xc8, cur only in slot 0xc0, the shadow base is s4 (x20) and SH is s5 (x21).

   WHAT IS HERE
   - the geometry of a cut of B10b (b10r_geoP / b10r_geo / b10r_SHb / b10r_sh_cell) and the frame chain at a call
     made at sp = s1 (b10r_chain);
   - the class-5 frame as a callee's argument: addressability from the frame's shadow cells (b10r_addr_frame),
     the live-frame arm of refuse_va_locs (b10r_fframe), and the two together as refuse_pre asks them
     (b10r_va_frame);
   - the closed call-site lemma of the bad-role refusal at 0x88978 (b10r_refuse_site, VERIFY rule 1j-bis): the
     state at the call supplies every premise PaFx.cl_callSF and refuse_c.refuse_contract ask besides afn_pre --
     the frame chain, the room for refuse's class-0 frame, the event bound, the argument ranges, refuse_pre with
     cur_name (F + 0x20, pf_nm's cstr_enc 16) and val (in buf, F + 0x40 .. F + 0x240) as its two %s arguments,
     and refuse's footprint inside parse_file's;
   - what refuse's journal keeps of the cut's state (b10r_keeps / b10r_keeps_call / b10r_keeps_refuse) and the
     cut facts re-derived at the state it returned at (b10r_base_move).
   Section hypotheses: none, except VRO (the listing's read-only range) and SSPX (the stack-protector cells at
   every AR state) on b10r_in_roP_img / b10r_base_move, which re-derive pf_obj's arodata_okP and sa_ssp after the
   call; both are listed in the segment's piece list, section 3. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= arithmetic and small tools (pf_seg_B11c_k.v's) ======================= *)
Lemma b10r_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b10r_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b10r_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Lemma b10r_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma b10r_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k ->
  getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b10r_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. lia. Qed.
Lemma b10r_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Ltac b10r_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b10r_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b10r_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
(* rounding up to the next multiple of 8 stays below an 8-aligned bound *)
Lemma b10r_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
intros x M H1 H2.
pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
lia.
Qed.
(* reader_pre's text bound (length s <= 65535)%nat, in Z *)
Lemma b10r_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
intros m H. apply Nat2Z.inj_le in H.
assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.
Lemma b10r_nth_firstn : forall {A} n (l : list A) k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros A n. induction n as [|n IH]; intros l k d Hk; [lia|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [firstn].
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
(* cur_name's C string (seg_spec.cstr_enc 16): its bytes, NUL and slack are the field's 16 bytes *)
Lemma b10r_nm_str : forall (rd : reader) a nm, a mod 8 = 0 -> pf_nm rd a nm ->
  sa_str rd a nm /\ (length nm < 16)%nat.
Proof.
  intros rd a nm Ha (f & Hb & Hl & Hn & Hz & Hf).
  assert (Hnth : forall i, (i < 16)%nat -> rd (a + Z.of_nat i) = Some (nth i (seg_spec.zs f) 0)).
  { intros i Hi. rewrite (Hb i ltac:(lia)). f_equal. unfold seg_spec.zs.
    rewrite <- (map_nth bv_unsigned f ZB0 i). apply nth_indep. rewrite length_map. lia. }
  split; [|exact Hn].
  split; [split; [|exact Hz]|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (Hnth i ltac:(lia)). f_equal. rewrite <- Hf. rewrite b10r_nth_firstn by lia. reflexivity.
  - intros x Hx.
    pose proof (Z.div_mod (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (a + Z.of_nat (length nm)) 8 ltac:(lia)) as M.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Ha in Da.
    replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
    rewrite (Hnth (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.

(* ======================= the bad-role format and its literal ======================= *)
Lemma b10r_lit_badrole : seg_litA_rc F_badrole = 0x21780.
Proof. vm_compute. reflexivity. Qed.
Lemma b10r_in_lits_badrole : In F_badrole PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. do 15 apply in_cons. apply in_eq. Qed.
Lemma b10r_badrole_fmt : In F_badrole seg_spec.REFUSE_FORMATS.
Proof. unfold seg_spec.REFUSE_FORMATS. do 10 apply in_cons. apply in_eq. Qed.
Lemma b10r_badrole_kinds : forall nm val : list Z,
  seg_spec.conv_kinds F_badrole = map seg_spec.arg_is_s [AS nm; AS val].
Proof. intros nm val. vm_compute. reflexivity. Qed.

(* ======================= the footprints ======================= *)
Lemma b10r_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
(* every byte refuse writes lies in [c + RC_REFUSAL, c + RC_OVERFLOW) *)
Lemma b10r_refuse_W_in_block : forall c rcs a, inFP (refuse_W c rcs) a ->
  c + seg_spec.RC_REFUSAL <= a < c + seg_spec.RC_OVERFLOW.
Proof.
intros c rcs a (r & Hr & Ha). unfold refuse_W in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat eqn:E; intros Hr; [|destruct Hr].
  apply Nat.ltb_lt in E.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF,
      seg_spec.RC_OVERFLOW in *; lia.
Qed.
Lemma b10r_refuse_W_pos : forall c rcs, 0 < c -> ~ YI16.sink_open_fp (refuse_W c rcs).
Proof.
intros c rcs Hc. apply sink_closed_pos. apply Forall_forall. intros r Hr. unfold refuse_W in Hr.
apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst]. unfold seg_spec.RC_REFUSED. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat; intros Hr; [|destruct Hr].
  destruct Hr as [<- | [<- | []]]; cbn [fst];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF; lia.
Qed.
Lemma b10r_refuse_W_sub : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a Ha. apply b10r_refuse_W_in_block in Ha.
exists (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW + 4). split.
- unfold seg_spec.RC_PARSE_W. right. left. reflexivity.
- cbn [fst snd]. lia.
Qed.

(* ======================= the frame's shadow cells at PF_SC_LOW ======================= *)
(* cur_name (cells 4, 5) and buf (cells 8 .. 71) are in scope at BAD *)
Lemma b10r_shb_low0 : forall i, (4 <= i < 6 \/ 8 <= i < 72) -> pf_shb PF_SC_LOW i = 0.
Proof.
intros i Hi. apply Z.eqb_eq.
destruct Hi as [Hi | Hi]; revert i Hi;
  [apply (b10r_zrange (fun i => pf_shb PF_SC_LOW i =? 0) 4 2)
  |apply (b10r_zrange (fun i => pf_shb PF_SC_LOW i =? 0) 8 64)]; vm_compute; reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* B's 23 setup slots (pf_pieces.v PF_SL) lie at s1 + 0x00 .. s1 + 0xd8 *)
Lemma b10r_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.
Lemma b10r_PF_SL_bounds : forall v pos, Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) (PF_SL v pos).
Proof. intros v pos. unfold PF_SL. repeat constructor; cbn [fst]; lia. Qed.
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ======================= the geometry of a cut of B10b ======================= *)
Definition b10r_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  in_app (pf_F v pos) 2048 /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b10r_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b10r_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = [(5, pos)] ++ frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc /\
  alloc_ceiling <= ly_stk_lo lyc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
pose proof HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b10r_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b10r_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
pose proof Happ as Happ'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | split; [exact HAR | subst lyc; exact Hceil]]]]].
unfold b10r_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|]. split; [exact Happ|].
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma b10r_SHb : forall v pos, b10r_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8) /\ pf_SH v pos mod 4 = 0.
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
assert (F4' : (pf_F v pos / 8) mod 4 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia.
  rewrite Z.div_mul by lia. replace (4 * q) with (q * 4) by lia. apply Z_mod_mult. }
unfold pf_SH, shadow_addr, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
rewrite Zplus_mod, F4'. reflexivity.
Qed.
Lemma b10r_F8 : forall v pos, b10r_geoP v pos -> pf_F v pos mod 8 = 0.
Proof.
intros v pos (_ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult.
Qed.
(* cell i of SH is the shadow byte of F + 8 i *)
Lemma b10r_sh_cell : forall v pos x, b10r_geoP v pos -> pf_F v pos <= x < pf_F v pos + 2048 ->
  shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8.
Proof.
intros v pos x HG Hx.
pose proof (b10r_F8 v pos HG) as HF8.
replace x with (pf_F v pos + (x - pf_F v pos)) at 1 by lia.
rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
reflexivity.
Qed.
(* a range of the class-5 frame whose shadow cells are 0 is addressable *)
Lemma b10r_addr_frame : forall v pos (rd : reader) sc q n, b10r_geoP v pos -> pf_fsh rd (pf_SH v pos) sc ->
  pf_F v pos + 32 <= q -> 0 <= n -> q + n <= pf_F v pos + 1088 ->
  (forall x, q <= x < q + n -> pf_shb sc ((x - pf_F v pos) / 8) = 0) ->
  sa_addr rd q n.
Proof.
intros v pos rd sc q n HG HF Hq Hn Hqn HZ.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & Fapp & _).
destruct (b10r_SHb v pos HG) as (ESH & SH1 & SH2 & EF8 & SH4).
pose proof alloc_ceiling_lt as HC.
pose proof (b10r_F8 v pos HG) as HF8.
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia]. destruct F4 as [F4|F4]; [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  rewrite (b10r_sh_cell v pos x HG ltac:(lia)).
  assert (B0 : 0 <= (x - pf_F v pos) / 8 < 144) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (HF ((x - pf_F v pos) / 8) B0). f_equal. exact (HZ x Hx).
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8)
    by exact (b10r_sh_cell v pos q HG ltac:(lia)).
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8)
    by exact (b10r_sh_cell v pos (q + n - 1) HG ltac:(lia)).
  assert (B1 : 4 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 136) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (pf_SH v pos) 4 ltac:(lia)) as D4. rewrite SH4 in D4.
  assert (Hlo : pf_SH v pos <= s).
  { assert (Q : (pf_SH v pos + (q - pf_F v pos) / 8) / 8 * 8 >= pf_SH v pos) by lia. lia. }
  assert (Hhi : s < pf_SH v pos + 144) by lia.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HF (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.
(* a range of the class-5 frame lies in a live side-stack frame *)
Lemma b10r_fframe : forall v pos lyc Sc q n, In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> sa_fframe lyc Sc q n.
Proof.
intros v pos lyc Sc q n Hin EF Hq Hn Hqn. exists 5, pos. split; [exact Hin|]. split; [lia|].
rewrite EF. change (fs_frame_bytes 5) with 2048. lia.
Qed.

(* ======================= the entry facts the call site needs ======================= *)
Lemma b10r_cx : forall v, pf_cx B v ->
  0 < p_c v /\ p_c v mod 16 = 0 /\ 0 <= p_c v < 2 ^ 64 /\ (length (p_s v) <= 65535)%nat /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\
  sa_room_n 2 (p_S v) /\ st_nev (p_S v) + EV_reac_segconf_parse_file <= EV_MAX.
Proof.
intros v (_ & _ & _ & Hc64 & _ & _ & _ & _ &
  (fe & (C0 & C16 & _ & _ & _ & _ & _ & _ & _ & _ & LS & _ & _ & DJ & _) & _) & HROOM & HEV).
split; [lia|]. split; [exact C16|]. split; [exact Hc64|]. split; [exact LS|].
split; [exact DJ|]. split; [exact HROOM | exact HEV].
Qed.
(* the frame chain at a call made at sp = s1 (s0 = sp0, the frame pointer) *)
Lemma b10r_chain : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct (b10r_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & _ & _ & _ & HAR & _).
pose proof HFI as (HJ & Hly & _ & _ & HSV & _).
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [lia | rewrite SPF; lia |].
    intros Hf. apply b10r_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. lia.
  + assert (E1 : Z_to_bv 5 1 = (1%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 0%nat 1 eq_refl) as H1. rewrite E1 in H1.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 0) with (pf_sp0 v - 8) in H1 by lia. exact H1.
  + assert (E8 : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; reflexivity).
    pose proof (HSV 1%nat 8 eq_refl) as H8. rewrite E8 in H8.
    replace (pf_sp0 v - 8 - 8 * Z.of_nat 1) with (pf_sp0 v - 16) in H8 by lia. exact H8.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D16. rewrite Hal, Z.add_0_r in D16. rewrite D16.
    replace (16 * (pf_sp0 v / 16)) with (2 * (pf_sp0 v / 16) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; lia | reflexivity].
Qed.

(* ======================= blocks at a state ======================= *)
Lemma b10r_heap_addr : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n -> sa_addr (rdW W mem) q n.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
pose proof alloc_ceiling_lt as Hac.
unfold sa_addr.
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin Hb ltac:(lia) Hn0).
Qed.
Lemma b10r_heap_bounds : forall ly S (W : world SEGS) mem md q n,
  AR SEGS B ly S W mem md -> sa_heap B ly S q n -> 0 <= n ->
  exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + n <= b + req_size m /\ 4096 <= b /\
    b + req_size m <= alloc_ceiling /\ in_app b (req_size m).
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hq) Hn.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Happ].
Qed.
Lemma b10r_heap_perm : forall ly S ly' S' q n, Permutation (ablocks B ly' S') (ablocks B ly S) ->
  sa_heap B ly S q n -> sa_heap B ly' S' q n.
Proof.
intros ly S ly' S' q n HP (b & m & Hin & Hb & Hq). exists b, m.
split; [exact (Permutation_in _ (Permutation_sym HP) Hin) | lia].
Qed.
Lemma b10r_band_not_app : forall b n s, in_app b n -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> ~ (b <= s < b + n).
Proof.
intros b n s Happ Hs Hin.
unfold in_app, SHADOW_OFF, kLowShadowBeg, YG0f.kHighMemBeg in *. lia.
Qed.

(* ======================= the image's objects at a later state ======================= *)
Lemma b10r_lit_move : forall (rd : reader) (W' : world SEGS) mem' a s, sa_lit SEGS B rd a s ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros rd W' mem' a s (Ha & ((Hz & Hn) & _) & Hp & Hr & Hi) K.
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He). rewrite (K _ Hm Ho He). exact (Hz i Hi').
Qed.
Lemma b10r_cat_move : forall (rd : reader) (W' : world SEGS) mem', sa_cat SEGS B rd catA ->
  (forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
     rdW W' mem' x = rd x) ->
  sa_cat SEGS B (rdW W' mem') catA.
Proof.
intros rd W' mem' (Hp & Hi & Hrows) K. split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp.
split; [|exact (b10r_lit_move rd W' mem' tp _ Hl K)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd (rdW W' mem')); [exact Htp|]. intros k Hk.
unfold pin_spec.row_addr, pin_spec.CAT_ROW in *.
destruct (Hi (catA + 296 * Z.of_nat i + k) ltac:(unfold pin_spec.CAT_BYTES; lia)) as (Hm & Ho & He).
exact (K _ Hm Ho He).
Qed.
Lemma b10r_sl_move : forall (rd rd' : reader) b L, pf_sl rd b L ->
  Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 0x100) L -> 0 <= b -> b + 0x100 <= 2 ^ 64 ->
  (forall a, b <= a < 2 ^ 64 -> rd' a = rd a) -> pf_sl rd' b L.
Proof.
intros rd rd' b L HL HB Hb Hb2 K. unfold pf_sl in *. rewrite Forall_forall in HL, HB |- *.
intros ov Hin. rewrite <- (HL ov Hin). apply rdword_ext. intros k Hk.
pose proof (HB ov Hin). apply K. lia.
Qed.
Lemma b10r_nm_move : forall v pos (rd rd' : reader) nm, pf_nm rd (pf_F v pos + PF_O_CN) nm ->
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rd' a = rd a) ->
  pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm (f & Hb & He) K. exists f. split; [|exact He].
intros i Hi. destruct He as (Hl & _). rewrite Hl in Hi. rewrite K; [exact (Hb i ltac:(lia))|].
change (fs_frame_bytes 5) with 2048. unfold PF_O_CN. lia.
Qed.

(* ======================= what a call made at s1 keeps of the cut's state ======================= *)
(* the stack from s1 up, the text and its NUL, the unowned image bytes, the class-5 frame and its shadow *)
Definition b10r_keeps (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 \/
             pf_SH v pos <= a < pf_SH v pos + fs_frame_bytes 5 / 8 ->
     rdW W2 mem2 a = rdW Wc memc a).
(* after a call made at sp = s1 whose footprint lies in the block c (refuse; any callee of that shape) *)
Lemma b10r_keeps_call : forall v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STKc (pf_s1 v) FPc lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  (forall a, inFP FPc a -> p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> ~ YI16.sink_open_fp FPc ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b10r_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc STKc FPc ly2 S2 W2 mem2 md2 k HB HJc NFP HCl HP2.
pose proof HB as (CX & FI & OBJ & _ & _).
destruct (b10r_geo v pos lyc Sc Wc rX memc mdc CX FI) as (G & Hfin & HFE & Hfrs & HAR & Hceil).
destruct (b10r_cx v CX) as (Hc0 & Hc16 & Hc64 & HLSn & HDJ & _ & _).
pose proof (b10r_le65535 _ HLSn) as HLS.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & GF1 & GF2 & GF3 & GF4 & GFapp & _).
destruct OBJ as (_ & _ & HT & _ & HC & _).
destruct (b10r_heap_bounds _ _ _ _ _ (p_t v) (pf_len v) HAR HT ltac:(unfold pf_len; lia))
  as (bt & mt & Hint & Hb1 & Hb2 & Hb3 & Hb4 & _).
destruct (b10r_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
unfold pf_len in Hb2.
split.
{ intros a Ha. apply F1; [lia | lia | intros Hf; apply NFP in Hf; unfold seg_spec.SEG_C_SIZE in *; lia]. }
split.
{ intros i Hi. replace (p_t v + i) with (bt + (p_t v + i - bt)) by lia.
  apply (F2 bt mt (p_t v + i - bt)); [exact Hint | exact (Permutation_in _ (Permutation_sym HP2) Hint) | lia |].
  intros Hf. apply NFP in Hf. unfold sa_disj, seg_spec.cstr_span in HDJ.
  pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
split.
{ intros a Ha Ho He. apply F3; [exact Ha | exact Ho | exact He |].
  apply fp_spares_closed; [exact HCl|].
  intros Hf. apply NFP in Hf. exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc bc mc a HAR Hinc ltac:(lia) Ha). }
intros a Ha. apply (F4 5 pos a Hfin).
- unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFE. unfold pf_SH in Ha. exact Ha.
- intros Hf. apply NFP in Hf. destruct Ha as [Ha | Ha].
  + pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFE in Hd. rewrite E5 in Ha, Hd.
    unfold seg_spec.SEG_C_SIZE in *. lia.
  + unfold pf_SH, shadow_addr in Ha. rewrite E5 in Ha. change (2048 / 8) with 256 in Ha.
    pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
    apply (b10r_band_not_app bc (req_size mc) a Hcapp); [lia|].
    unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* after refuse: its footprint refuse_W lies in the block c (refusal[n], n_refusals, refused) *)
Lemma b10r_keeps_refuse : forall v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 (W2 : world SEGS) mem2 md2 k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b10r_keeps v pos Wc memc W2 mem2.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc cf ly2 S2 W2 mem2 md2 k HB HJc HP2.
destruct (b10r_cx v (proj1 HB)) as (Hc0 & _).
apply (b10r_keeps_call v pos lyc Sc Wc rX memc mdc sc STK_refuse (refuse_W (p_c v) cf) ly2 S2 W2 mem2 md2 k HB HJc);
  [| exact (b10r_refuse_W_pos _ cf Hc0) | exact HP2].
intros a Ha. apply b10r_refuse_W_in_block in Ha. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW,
  seg_spec.SEG_C_SIZE in *. lia.
Qed.

(* ======================= refuse's premises at the call 0x88978 ======================= *)
(* one %s argument in the class-5 frame whose cells are 0 and whose 8-rounded span ends at M *)
Lemma b10r_va_frame : forall v pos lyc Sc (Wc : world SEGS) memc mdc sc (rd : reader) q s sp (k : nat) M,
  b10r_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_fsh rd (pf_SH v pos) sc -> sa_str rd q s -> (length s <= 65535)%nat ->
  pf_F v pos + 32 <= q -> q + Z.of_nat (length s) + 1 <= M -> M mod 8 = 0 -> M <= pf_F v pos + 1088 ->
  (forall x, q <= x < q + Z.of_nat (length s) + 1 -> pf_shb sc ((x - pf_F v pos) / 8) = 0) ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE -> (k <= 8)%nat -> alloc_ceiling <= ly_stk_lo lyc ->
  sa_va_arg rd
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)] (w64 q) (AS s) /\
  sa_fframe lyc Sc q (Z.of_nat (length s) + 1).
Proof.
intros v pos lyc Sc Wc memc mdc sc rd q s sp k M HG HAR Hin EF HF HS HL Hq HM HM8 HMF HZ Hc Hk Hceil.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
assert (EQ : bv_unsigned (w64 q) = q) by (apply b10r_w64_u; lia).
split; [|apply (b10r_fframe v pos lyc Sc q _ Hin EF); lia].
cbn [sa_va_arg]. rewrite EQ.
split; [lia|]. split; [exact HS|]. split; [exact HL|].
split; [apply (b10r_addr_frame v pos rd sc q (Z.of_nat (length s) + 1) HG HF Hq ltac:(lia) ltac:(lia)
          ltac:(intros x Hx; apply HZ; lia))|].
pose proof (b10r_round8 (q + Z.of_nat (length s) + 1) M HM HM8) as HR.
assert (HSP : q + seg_spec.cstr_span q s <= M) by (unfold seg_spec.cstr_span; lia).
destruct Hc as (b & m & Hb & Hb1 & Hb2).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hsep.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EF in Hsep. change (fs_frame_bytes 5) with 2048 in Hsep.
assert (HAP : q + seg_spec.cstr_span q s <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= q)
  by (destruct Hsep as [Hs|Hs]; [right|left]; lia).
unfold sa_apart_all, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
  seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *.
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_nil.
Qed.

(* VERIFY rule 1j-bis at 0x88978: the state at the call gives every premise of PaFx.cl_callSF and of
   refuse_contract besides afn_pre (which the call rule builds from the journal) *)
Lemma b10r_refuse_site : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (regsc : bvmap 5 word),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) vp val -> pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  getr regsc 10 = w64 (p_c v) -> getr regsc 11 = w64 (ln + 1) ->
  getr regsc 12 = w64 (seg_litA_rc F_badrole) ->
  getr regsc 13 = w64 (pf_F v pos + PF_O_CN) -> getr regsc 14 = w64 vp ->
  (exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1) /\
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  0 <= p_c v < 2 ^ 64 /\ 0 <= ln + 1 < 2 ^ 64 /\ 0 <= seg_litA_rc F_badrole < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1)
    (seg_litA_rc F_badrole) [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17]
    cf (ln + 1) F_badrole [AS nm; AS val] /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX /\
  (forall a, inFP (refuse_W (p_c v) cf) a ->
     (inFP (seg_spec.RC_PARSE_W (p_c v)) a /\
      exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) \/
     in_tmp_block (ablocks B (p_ly v) (p_S v)) (ablocks B lyc Sc) a).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regsc HB HMID HST HVS HVI R10 R11 R12 R13 R14.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10r_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR & Hceil).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b10r_cx v HCX) as (Hc0 & Hc16 & HcB & HLSn & _ & HROOM & HEV).
pose proof (b10r_le65535 _ HLSn) as LSZ.
pose proof HFI as (HJ & Hly & _ & _ & _ & _ & HFRM & HTF & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _).
destruct HOBJ as (_ & _ & _ & Ac & Hc & _ & LITS & HROD & SSP).
destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
pose proof HRC as (bs & _ & (_ & _ & _ & _ & HK8 & _)).
destruct HMID as (Ho & Hle & Hlctx).
destruct (pf_lctx_ln _ _ _ _ Hlctx) as (Hln & Hnx).
pose proof (pf_next_le (p_s v) o Ho) as HNL.
assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
pose proof asan_consts as (AC1 & _).
pose proof (LITS F_badrole b10r_in_lits_badrole) as HLF.
(* the two %s arguments: cur_name at F + 0x20 and val in buf *)
assert (HF8 : pf_F v pos mod 8 = 0) by exact (b10r_F8 v pos HGEO).
assert (FCN8 : (pf_F v pos + PF_O_CN) mod 8 = 0) by (unfold PF_O_CN; rewrite Zplus_mod, HF8; reflexivity).
destruct (b10r_nm_str _ _ nm FCN8 HNM) as [HNS HNL16].
destruct HVI as [HV1 HV2].
assert (HZ0 : forall lo hi x, (4 <= lo /\ hi <= 6) \/ (8 <= lo /\ hi <= 72) ->
    pf_F v pos + 8 * lo <= x < pf_F v pos + 8 * hi -> pf_shb PF_SC_LOW ((x - pf_F v pos) / 8) = 0).
{ intros lo hi x Hlh Hx. apply b10r_shb_low0.
  assert (Q1 : lo <= (x - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Q2 : (x - pf_F v pos) / 8 < hi) by (apply Z.div_lt_upper_bound; lia).
  lia. }
assert (VA1 := b10r_va_frame v pos lyc Sc Wc memc mdc PF_SC_LOW (rdW Wc memc) (pf_F v pos + PF_O_CN) nm
  (spZ regsc) (length (rc_refusal cf)) (pf_F v pos + 0x30) HGEO HAR Hin EF HFSH HNS
  ltac:(apply (Nat.le_trans _ 16%nat); [lia | apply Nat.leb_le; vm_compute; reflexivity])
  ltac:(unfold PF_O_CN; lia) ltac:(unfold PF_O_CN; lia)
  ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)
  ltac:(intros x Hx; apply (HZ0 4 6); [left; lia | unfold PF_O_CN in Hx; lia]) Hc HK8 Hceil).
assert (VA2 := b10r_va_frame v pos lyc Sc Wc memc mdc PF_SC_LOW (rdW Wc memc) vp val
  (spZ regsc) (length (rc_refusal cf)) (pf_F v pos + 0x240) HGEO HAR Hin EF HFSH HVS
  ltac:(apply (Nat.le_trans _ 512%nat);
          [unfold PF_O_BUF in HV1, HV2; lia | apply Nat.leb_le; vm_compute; reflexivity])
  ltac:(unfold PF_O_BUF in HV1; lia) ltac:(unfold PF_O_BUF in HV2; lia)
  ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)
  ltac:(intros x Hx; apply (HZ0 8 72); [right; lia | unfold PF_O_BUF in HV1, HV2; lia]) Hc HK8 Hceil).
destruct VA1 as [VA1 FF1]. destruct VA2 as [VA2 FF2].
destruct (b10r_heap_bounds _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR Hc ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hcb1 & Hcb2 & _).
split; [exact (b10r_chain v pos lyc Sc Wc rX memc mdc HCX HFI)|].
split; [exact HROD|].
split; [exact HcB|]. split; [lia|]. split; [rewrite b10r_lit_badrole; lia|].
split.
{ unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact HRC|]. split; [exact Hc|]. split; [exact Ac|].
  split; [destruct HCNT as [HC1 _]; lia|].
  split; [exact HLN|]. split; [reflexivity|].
  split; [exact b10r_badrole_fmt|]. split; [apply b10r_badrole_kinds|].
  split; [rewrite b10r_lit_badrole; lia|]. split; [reflexivity|]. split; [exact HLF|].
  split.
  { rewrite R13, R14. cbn [sa_va_args]. split; [exact VA1|]. split; [exact VA2 | exact I]. }
  split.
  { rewrite R13, R14. cbn [refuse_va_locs].
    rewrite (b10r_w64_u (pf_F v pos + PF_O_CN)) by (unfold PF_O_CN; lia).
    rewrite (b10r_w64_u vp) by (unfold PF_O_BUF in HV1, HV2; lia).
    split; [right; exact FF1|]. split; [right; exact FF2 | exact I]. }
  split; [exact HFRM|]. split; [exact SSP|].
  intros x Hx. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hx. }
split.
{ unfold sa_room. unfold sa_room_n in HROOM. rewrite Hfr, length_app. cbn [length]. lia. }
split.
{ unfold EV_refuse. unfold EV_reac_segconf_parse_file in HEV. lia. }
intros a Ha. left. split; [exact (b10r_refuse_W_sub _ _ a Ha)|].
exists bc, mc. split; [exact Hinc|]. apply b10r_refuse_W_in_block in Ha.
unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia.
Qed.

(* ======================= the cut facts at the state refuse returned at ======================= *)
Section m.
(* the image's read-only range is the listing's (SegObj.v; the pinned instance gives it by computation) *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the image-A owner's route A: the stack-protector cells at every AR state (image B's stage-2 SegRecCells gives it) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Lemma b10r_relro_img : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof.
intros a Ha. destruct VRO as [Hlo Hhi]. apply pa_relro_img. rewrite Hlo, Hhi.
unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Ha. lia.
Qed.
Lemma b10r_in_roP_img : forall a, in_roP SEGS RLO_A RHI_A a -> in_img SEGS a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (b10r_relro_img a Hr)].
Qed.

Lemma b10r_base_move : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc sc ly2 S2 (W2 : world SEGS) regs2
  mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b10r_keeps v pos Wc memc W2 mem2 ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 sc.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc sc ly2 S2 W2 regs2 mem2 md2 HB Hfx HJ2 Hly2 (f2 & HS2) HP2
  (K1 & K2 & K3 & K4) KR.
pose proof HB as (CX & FI & OBJ & SL & FSH).
destruct (b10r_geo v pos lyc Sc Wc rX memc mdc CX FI) as (G & Hfin & HFE & Hfrs & HAR & Hceil).
destruct (b10r_cx v CX) as (Hc0 & Hc16 & HcB & HLSn & _ & _ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & GF1 & GF2 & GF3 & GF4 & GFapp & _).
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
destruct OBJ as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2.
pose proof alloc_ceiling_lt as Hac.
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
split; [exact CX|].
split.
{ split; [exact HJ2|]. split; [rewrite Hly2; exact Hly|].
  split; [exists f2; rewrite HS2, HSf; reflexivity|].
  split; [exact (Permutation_trans HP2 HPerm)|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K1. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply K4. left. rewrite E5. lia. }
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
  split; [exact HTF|].
  split.
  { apply (b10r_sl_move (rdW Wc memc) _ (pf_s1 v) _ HC8); [repeat constructor; cbn [fst]; lia | lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (b10r_heap_bounds lyc Sc Wc memc mdc (p_t v) (pf_len v) HAR HT ltac:(unfold pf_len; lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (pf_len v)) by exact (b10r_heap_perm _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (b10r_heap_perm _ _ _ _ _ _ HP2 HC).
  unfold pf_len in Hbt2.
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (b10r_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(unfold pf_len; lia))|].
  split; [exact HT2|].
  split; [exact (b10r_heap_addr ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (b10r_cat_move _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (b10r_lit_move _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho He; rewrite (K3 a (b10r_in_roP_img a Hro) Ho He); exact (ROD a Hro Ho He)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split.
{ apply (b10r_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (b10r_PF_SL_bounds v pos)); [lia | lia |].
  intros a Ha. apply K1. exact Ha. }
intros i Hi. rewrite K4; [exact (FSH i Hi)|]. right. rewrite E5. change (2048 / 8) with 256. lia.
Qed.
End m.
End e.
End f.
End d.
