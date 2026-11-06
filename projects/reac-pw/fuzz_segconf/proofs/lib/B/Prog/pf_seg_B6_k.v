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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 534 of its 586 lines of code are new or changed and 401 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B11b_k.v; 344 of its 495 lines of code are new or changed and 435 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the kit of
   segment B6 of reac_segconf_parse_file's walk (the B6 segment lane of the image-B G3 walk owner, 2026-10-30).
   proves no function (kind: walk kit).
   ADAPTED from the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a5_k.v and pf_a2_g.v (commit 01534c6baa27)
   through the image-B form of the image-B G3 walk owner's B10b segment lane (its lib/B/Prog/pf_seg_B10b_j.v, which carries B's
   352-byte frame, s1 in [sp0 - 368, sp0 - 352], STK 12832, the 23 slots of PF_SL at s1 + 0x00 .. 0xd8, c's slot
   0xc8 and cur's slot 0xc0, and the shadow base in s4 = x20): copied under the prefix b6_ and re-derived for
   segment B6's own write set.
   WHAT B6 WRITES (plan section 5.2 row B6, 0x88258-0x882bc): the callees' stack windows below s1 (strspn at
   0x88260, refuse at 0x882b4) and the cur slot s1 + 0xc0 (0x882a0 `sd a1,192(s1)`). It writes no byte of buf, no
   shadow cell of the class-5 frame and no other slot, so EVERY byte below the allocator's ceiling is kept: the
   text, the block c, the frame, the frame's shadow, the literals, the catalogue and the stack-protector cells
   are all below it (b6_out). The refuse call does not keep that set (it writes c->refused, c->refusal[n] and
   c->n_refusals); the file that walks REF3 rebuilds the cut from refuse's own ajournal, for which this kit gives
   the geometry, the chain, the text facts, the footprint inclusion b6_rfw_sub and the AR re-derivations
   b6_addr_of_heap / b6_tail_of_heap. *)
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

(* ---------- arithmetic and small tools (A's pf_a2_g.v / pf_a2.v, through B10b's copy) ---------- *)
Lemma b6_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b6_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b6_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b6_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Lemma b6_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma b6_rg_pres : forall r1 r2 L, aregs_preserved r1 r2 -> Forall (fun rv => acallee_saved (fst rv)) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.
Ltac b6_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b6_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b6_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* ---------- the footprints ---------- *)
Lemma b6_rcw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING,
  seg_spec.RC_GEN in *.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
(* refuse's footprint lies inside parse_file's own: c->refused, c->refusal[n] and c->n_refusals are all inside
   [c + RC_REFUSAL, c + RC_OVERFLOW + 4), RC_PARSE_W's second range, since n < 8 whenever refuse records one *)
Lemma b6_rfw_rng : forall c rcs a, inFP (refuse_W c rcs) a ->
  c + seg_spec.RC_REFUSAL <= a /\ a < c + seg_spec.RC_OVERFLOW + 4.
Proof.
intros c rcs a (r & Hr & Ha). unfold refuse_W in Hr.
destruct ((length (rc_refusal rcs) <? 8)%nat) eqn:E.
- assert (Hn : (length (rc_refusal rcs) < 8)%nat) by (apply Nat.ltb_lt; exact E).
  assert (Hz : Z.of_nat (length (rc_refusal rcs)) <= 7) by lia.
  assert (Hz0 : 0 <= Z.of_nat (length (rc_refusal rcs))) by lia.
  cbn [app In] in Hr.
  unfold seg_spec.refusal_addr in *.
  unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF,
    seg_spec.RC_OVERFLOW in *.
  destruct Hr as [HE | [HE | [HE | []]]]; rewrite <- HE in Ha; clear HE; cbn [fst snd] in Ha;
    destruct Ha as [Ha1 Ha2]; split; lia.
- cbn [app In] in Hr.
  unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *.
  destruct Hr as [HE | []]; rewrite <- HE in Ha; cbn [fst snd] in Ha; split; lia.
Qed.
Lemma b6_rfw_sub : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a H. pose proof (b6_rfw_rng c rcs a H) as [H1 H2].
exists (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW + 4).
split; [unfold seg_spec.RC_PARSE_W; apply in_cons; apply in_eq|]. cbn [fst snd]. exact (conj H1 H2).
Qed.
Lemma b6_rfw_in : forall c rcs a, inFP (refuse_W c rcs) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof. intros c rcs a H. exact (b6_rcw_in c a (b6_rfw_sub c rcs a H)). Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma b6_RL_cs : forall v pos, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos).
Proof. intros v pos. unfold PF_RL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Lemma b6_RM_cs : forall v o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RM v o ln).
Proof. intros v o ln. unfold PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. Qed.
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Lemma b6_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x00 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.
(* no slot of PF_SL is the cur slot 0xc0: each is 8 bytes and either ends at or below 0xc0, or starts at 0xc8 *)
Lemma b6_PF_SL_notcur : forall v pos ov, In ov (PF_SL v pos) -> fst ov + 8 <= 0xc0 \/ 0xc8 <= fst ov.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ---------- reading a region the run wrote (pf_a2.v) ---------- *)
Definition b6_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma b6_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> b6_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.
Lemma b6_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.

(* ---------- the geometry of a B6 cut, and what a B6 step keeps ---------- *)
(* B6's writes: the callees' stack windows below s1 and the cur slot s1 + 0xc0, both at or above the ceiling *)
Definition b6_Wr (v : pfv) (a : Z) : Prop :=
  (pf_sp0 v - 12832 <= a < pf_s1 v) \/ (pf_s1 v + 0xc0 <= a < pf_s1 v + 0xc8).
Definition b6_kept (v : pfv) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ b6_Wr v a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Definition b6_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos).
Lemma b6_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b6_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
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
pose proof (b6_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b6_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | split; [exact HAR | exact Hly]]]]].
unfold b6_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. lia.
Qed.
Lemma b6_SHb : forall v pos, b6_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b6_geoP v pos.
(* every byte the walk's objects name lies below the allocator's ceiling, and so does its shadow cell; both of
   B6's write ranges lie at or above the ceiling *)
Definition b6_out (x : Z) : Prop := 0 <= x < alloc_ceiling.
Lemma b6_out_nw : forall x, b6_out x ->
  0 <= x < 2 ^ 64 /\ ~ b6_Wr v x /\ 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b6_Wr v (SHADOW_OFF + x / 8).
Proof.
intros x (Hx0 & Hx1).
pose proof G as (S1 & S2 & S3 & S4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0.
pose proof (Z.div_le_mono x 0x7fffff800000 8 ltac:(lia) ltac:(lia)) as D1.
change (0x7fffff800000 / 8) with 0xffffff00000 in D1.
unfold b6_Wr, SHADOW_OFF.
split; [lia|]. split; [intros [W | W]; lia|]. split; [lia|]. intros [W | W]; lia.
Qed.
Lemma b6_out_img : forall x, 0x10000 <= x < kImgEnd -> b6_out x.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _). unfold b6_out, kImgEnd in *. lia.
Qed.
Lemma b6_out_inimg : forall x, in_img SEGS x -> b6_out x.
Proof. intros x Hx. apply b6_out_img. exact (pa_img_range x Hx). Qed.
Lemma b6_out_frame : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> b6_out a.
Proof. intros a Ha. pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _). unfold b6_out. lia. Qed.
(* the real stack (the saved registers, the slots at or above s1) is outside the two write ranges, except the
   cur slot itself *)
Lemma b6_stack_nw : forall a, pf_s1 v <= a -> a + 8 <= pf_sp0 v ->
  (a + 8 <= pf_s1 v + 0xc0 \/ pf_s1 v + 0xc8 <= a) ->
  forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ ~ b6_Wr v (a + k).
Proof.
intros a Ha1 Ha2 Ha3 k Hk. pose proof G as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
unfold b6_Wr. split; [lia|]. intros [W | W]; lia.
Qed.
Lemma b6_saved_nw : forall a, pf_sp0 v - 104 <= a -> a + 8 <= pf_sp0 v ->
  forall k, 0 <= k < 8 -> 0 <= a + k < 2 ^ 64 /\ ~ b6_Wr v (a + k).
Proof.
intros a Ha1 Ha2 k Hk. pose proof G as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
unfold b6_Wr. split; [lia|]. intros [W | W]; lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : b6_kept v rd rd'.
Lemma b6_k_byte : forall x, b6_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (b6_out_nw x Hx) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma b6_k_shadow : forall x, b6_out x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (b6_out_nw x Hx) as (_ & _ & H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma b6_k_zs : forall p l, (forall i, (i < length l)%nat -> b6_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b6_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b6_k_bytes : forall p l, (forall i, (i < length l)%nat -> b6_out (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (b6_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b6_k_rdword : forall a, (forall k, 0 <= k < 8 -> b6_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (b6_k_byte _ (Ho k Hk)). Qed.
Lemma b6_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma b6_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b6_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> b6_out x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
pose proof (Ho (p + Z.of_nat (length s)) ltac:(lia)) as He. unfold b6_out in He.
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (b6_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (b6_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma b6_k_addr : forall q n, (forall x, q <= x < q + n -> b6_out x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (b6_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b6_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b6_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b6_k_str a s); [|exact Hs]. intros x Hx. apply b6_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma b6_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b6_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (b6_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply b6_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b6_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (b6_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply b6_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply b6_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b6_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> b6_out (a + k))
  by (intros a Ha k Hk; apply b6_out_img; lia).
split; [rewrite (b6_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b6_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* a range inside a live heap block lies below the allocator's ceiling *)
Lemma b6_out_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc b m x,
  b6_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m ->
  b6_out x.
Proof.
intros v pos lyc Sc Wc memc mdc b m x HG HAR Hb Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _).
unfold b6_out. lia.
Qed.
Lemma b6_out_sa_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  b6_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> sa_heap B lyc Sc q n -> q <= x < q + n -> b6_out x.
Proof.
intros v pos lyc Sc Wc memc mdc q n x HG HAR (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
apply (b6_out_heap v pos lyc Sc Wc memc mdc b m x HG HAR Hb). lia.
Qed.

(* ---------- the cut's objects, carried across a B6 step ---------- *)
Lemma b6_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  b6_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> b6_kept v rd rd' ->
  pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> b6_out x)
  by (intros x Hx; exact (b6_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR H3 Hx)).
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> b6_out x)
  by (intros x Hx; exact (b6_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR H5 Hx)).
split; [apply (b6_k_str v pos HG rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (b6_k_addr v pos HG rd rd' K _ _ Ht H2)|]. split; [exact H3|].
split; [exact (b6_k_addr v pos HG rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (b6_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (b6_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (b6_k_rod v pos HG rd rd' K H8) | exact (b6_k_ssp v pos HG rd rd' K H9)].
Qed.
Lemma b6_keep_rconf : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf,
  b6_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> b6_kept v rd rd' ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE -> sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf HG HAR K Hh (bs & Hb & Henc).
exists bs. split; [|exact Henc]. apply (b6_k_bytes v pos HG rd rd' K); [|exact Hb].
intros i Hi. destruct Henc as [Hl _].
apply (b6_out_sa_heap v pos lyc Sc Wc memc mdc _ _ _ HG HAR Hh). lia.
Qed.
Lemma b6_keep_nm : forall v pos rd rd' nm, b6_geoP v pos -> b6_kept v rd rd' ->
  pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm HG K (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN.
rewrite (b6_k_byte v pos HG rd rd' K); [exact (Hb i ltac:(lia))|].
apply (b6_out_frame v pos HG). unfold PF_O_CN. lia.
Qed.
Lemma b6_keep_fsh : forall v pos rd rd' sc, b6_geoP v pos -> b6_kept v rd rd' ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sc HG K H i Hi.
destruct (b6_SHb v pos HG) as (ESH & SH1 & SH2 & F8). pose proof asan_consts as (C1 & _).
rewrite (proj1 K (pf_SH v pos + i)); [exact (H i Hi) | lia |].
pose proof HG as (S1 & S2 & S3 & S4 & _). unfold b6_Wr. intros [W | W]; lia.
Qed.
Lemma b6_keep_saved : forall v pos rd rd' regs, b6_geoP v pos -> b6_kept v rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs HG K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
intros k Hk. destruct (b6_saved_nw v pos HG (pf_sp0 v - 8 - 8 * Z.of_nat j) ltac:(lia) ltac:(lia) k Hk) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma b6_keep_flag : forall v pos rd rd', b6_geoP v pos -> b6_kept v rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos rd rd' HG K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (b6_out_nw v pos HG (pf_F v pos + 2048 - 8 + k)
  ltac:(apply (b6_out_frame v pos HG); lia)) as (H0 & H1 & _).
exact (proj1 K _ H0 H1).
Qed.
(* a slot of the real frame other than the cur slot *)
Lemma b6_keep_slot : forall v pos rd rd' off w, b6_geoP v pos -> b6_kept v rd rd' ->
  0 <= off -> off <= 0xd8 -> (off + 8 <= 0xc0 \/ 0xc8 <= off) ->
  rdword rd (pf_s1 v + off) = Some w -> rdword rd' (pf_s1 v + off) = Some w.
Proof.
intros v pos rd rd' off w HG K H0 H1 H2 H. rewrite (rdword_ext rd rd'); [exact H|].
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
intros k Hk. destruct (b6_stack_nw v pos HG (pf_s1 v + off) ltac:(lia) ltac:(lia) ltac:(lia) k Hk) as (Q0 & Q1).
exact (proj1 K _ Q0 Q1).
Qed.
Lemma b6_keep_sl : forall v pos rd rd', b6_geoP v pos -> b6_kept v rd rd' ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' HG K H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
pose proof (b6_PF_SL_offs v pos ov Hov) as Ho. pose proof (b6_PF_SL_notcur v pos ov Hov) as Hn.
exact (b6_keep_slot v pos rd rd' (fst ov) (snd ov) HG K ltac:(lia) ltac:(lia) Hn (H ov Hov)).
Qed.

(* ---------- the text, the read-only view, the frame chain ---------- *)
Lemma b6_text : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ~ In 0 (p_s v) /\ (length (p_s v) <= 65535)%nat /\ sa_str (rdW Wc memc) (p_t v) (p_s v) /\
  sa_addr (rdW Wc memc) (p_t v) (pf_len v) /\ sa_heap B lyc Sc (p_t v) (pf_len v) /\
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE /\
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\
  p_t v <> 0 /\ p_c v <> 0 /\ p_c v mod 16 = 0 /\
  rc_refused (p_rcs v) + 2 ^ 17 < 2 ^ 32 /\ rc_overflow (p_rcs v) + 2 ^ 17 < 2 ^ 32.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & _ & HOBJ & _).
destruct HOBJ as (HSTR & HADDR & HHEAP & _ & HC & _).
destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
destruct HPF as (HRP & _).
destruct HRP as (C0 & C16 & _ & _ & _ & _ & RF & OV & T0 & _ & HLS & _ & _ & DJ & _).
split; [exact (proj2 (proj1 HSTR))|]. split; [exact HLS|].
split; [exact HSTR|]. split; [exact HADDR|]. split; [exact HHEAP|]. split; [exact HC|].
split; [exact DJ|]. split; [exact T0|]. split; [exact C0|]. split; [exact C16|]. split; [exact RF | exact OV].
Qed.
Lemma b6_rom : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (_ & _ & HOBJ & _). destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
intros a (sg & Hsg & Hw & Hr) Ho He. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* the frame chain at a call from B6 (s0 = sp0): the prologue's record (ra at sp0 - 8, the entry s0 at sp0 - 16,
   pf_saved) on afn_pre's chain, which the journal keeps above sp0 *)
Lemma b6_chain : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (pf_sp0 v) ch1.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof HB as (HCX & HFI & _).
destruct (b6_geo v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR & Hly).
destruct HFI as (HJ & _ & _ & _ & HSV & _).
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
pose proof HPRE as (HAR0 & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & _ & _ & _ & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
subst lyc.
destruct HPF as (HRP & _). destruct HRP as (_ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR0 Hbc) as (_ & _ & Hcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
pose proof G as (S1 & S2 & S3 & S4 & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *.
pose proof asan_consts as (C1 & _).
destruct (Z_lt_le_dec (pf_sp0 v) (ly_top (p_ly v) - 16)) as [Hlt | Hge].
- exists ((pf_sp0 v, raZ (p_regs v), s0Z (p_regs v)) :: p_ch v).
  apply (achain_push (p_ly v) (rdW (p_W v) (p_mem v)) (rdW Wc memc) (pf_sp0 v) (s0Z (p_regs v)) (raZ (p_regs v))
    (p_ch v) (pf_s1 v) Hch).
  + lia.
  + intros a Ha. apply F1; [lia | lia |].
    intros Hf. apply b6_rcw_in in Hf. unfold seg_spec.SEG_C_SIZE in *. lia.
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
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* ---------- re-derivation from AR at a later state ---------- *)
(* a range inside a live heap block is addressable, with its shadow words visible, at that state *)
Lemma b6_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
  0 <= q -> 0 < n -> sa_addr (rdW W mem) q n /\ q + n <= alloc_ceiling.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hm) Hq Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _).
split; [|lia].
split; [lia|]. split; [lia|].
split; [exact (amem_range_sub_app b (req_size m) q n Happ Hc ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.
(* the slack of the 8-byte word holding a C string's NUL, at any AR state where the string is in a live block *)
Lemma b6_tail_of_heap : forall ly S (W : world SEGS) mem md q (s : list Z),
  AR SEGS B ly S W mem md -> sa_heap B ly S q (Z.of_nat (length s) + 1) ->
  sa_tail (rdW W mem) (q + Z.of_nat (length s)).
Proof.
intros ly S W mem md q s HAR (b & m & Hin & Hb & Hm) x Hx.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
apply (AR_block_word_vis SEGS B ly S W mem md b m (q + Z.of_nat (length s)) x HAR Hin); lia.
Qed.
End x.
End d.
