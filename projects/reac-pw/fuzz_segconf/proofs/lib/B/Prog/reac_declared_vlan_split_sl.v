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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 324 of its 370 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the point KL (listing 0x54fc, image B
   0x8a2bc), the head of the digit loop, pass j (vs_KL_stmt j, reac_declared_vlan_split_d.v). Image A's walk has no
   KL lemma yet (commit ceb7e39832b2 has K6 and KR only), so this file is written for image B.
   One pass:
     0x8a2bc `addi a5,a5,-48`, 0x8a2c0 `bltu a2,a5` -> 0x8a320: the byte dot[1 + j] is no digit
       (vs_digit_test); then `li a0,0` and the epilogue KR, and vlan_split s = None (vs_none_nodigit);
     0x8a2c4 `beq a4,a3` -> unimp 0x8a3d8: the UBSan trap of a4 + 1 (a4 = dot + 1 + j, a3 = -1), never taken;
     0x8a2c8-0x8a2d4 the instrumented check of the load1 of a1 = dot + 2 + j (shadow byte at (a1 >> 3) + s6, slow
       path 0x8a2ec-0x8a2f0, error path 0x8a2f4-0x8a2f8): the run leaves its obligation, which the segment's
       addressable range [segment, segment + length s + 1) (split_pre's sa_addr) discharges;
     0x8a2d8 `addi a4,a4,1`, 0x8a2dc `lbu a5,0(a4)` (dot[2 + j], the seed's atom 40), 0x8a2e0 `addi a1,a1,1`,
       0x8a2e4 `beqz a5` -> 0x8a2fc (K2: the tail is all digits), else 0x8a2e8 `j 0x8a2bc` (KL, pass j + 1).
   The loop writes no byte. vs_KL closes the passes by induction on 15 - j (length s < 16). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the byte dot[2 + j] the pass loads (`lbu a5,0(a4)` after `addi a4,a4,1`): one byte at a4 + 1, the seed's atom 40 *)
Definition vsl_r : YP09.region := YP09.mkRegion (Some 14%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 40 0))].
Definition vsl_Bx : sv := SOff 22 0.
Definition vsl_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the seed facts at KL: a1 = dot + 2 + j and a4 = dot + 1 + j below 2^47 (split_pre's amem_range of the segment),
   a2 = 9, a3 = -1, the next byte a byte *)
Definition vsl_fs : list (nat * afact) :=
  [(11%nat, mkAF 0 (2 ^ 47 - 1) 0); (12%nat, mkAF 9 9 0); (13%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0);
   (14%nat, mkAF 0 (2 ^ 47 - 1) 0); (40%nat, mkAF 0 255 0)].

(* a run over regions with no write window keeps every byte *)
Ltac vsl_nowin_tac :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin.
(* HM : the memory of the current state is mem' at every address (chained across runs) *)
Ltac vsl_mem HF :=
  lazymatch type of HF with frame_of _ _ ?m ?m' =>
  let Hx := fresh "Hx" in
  assert (Hx : forall x, m' x = m x) by (let x := fresh "x" in intros x; apply HF; vsl_nowin_tac);
  lazymatch goal with
  | H0 : forall x, m x = ?m0 x |- _ =>
    let Hy := fresh "Hy" in
    assert (Hy : forall x, m' x = m0 x) by (let x := fresh "x" in intros x; rewrite Hx; apply H0);
    clear Hx H0; rename Hy into HM
  | _ => rename Hx into HM
  end end.
(* the registers a run left as their atoms *)
Ltac vsl_keep HS EV :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hcases := fresh "Hcases" in
  intros r Hr;
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 22 \/ r = 23 \/ r = 24 \/
    r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hcases as [-> | Hcases]); try subst r;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let n := eval compute in (Z.to_nat k) in
    eapply (vs_reg_atom _ _ _ _ _ n _ HS);
    [repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity | vm_compute; reflexivity] end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma vsl_rd_eq : forall (W : world SEGS) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, rdW W m' a = rdW W m a.
Proof using. intros W m m' Hm a. apply (aview_eq_of SEGS). unfold mrestrict. rewrite Hm. reflexivity. Qed.
Lemma vsl_byte : forall (H : word -> bool) m a v, aview SEGS H m a = Some v -> 0 <= v < 256.
Proof using.
intros H m a v E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m) a) as [b|]; [|discriminate]. cbn in E. injection E as <-.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.
Lemma vsl_mbyte : forall (H : word -> bool) m a z, aview SEGS H m a = Some z ->
  mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 z).
Proof using.
intros H m a z Ha. unfold aview in Ha. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* the body of le_byte v 1 0 (val_mem's le_byte is lib/Reusable/YO0f.v's, the same text as the kit's) *)
Lemma vsl_le1 : forall v, 0 <= v < 256 -> (Z.shiftr (v mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0)) mod 256 = v.
Proof using.
intros v Hv. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma vsl_ra_kept : forall (rd rd' : reader) a n,
  range_addressable rd SHADOW_OFF a n ->
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd' SHADOW_OFF a n.
Proof using. intros rd rd' a n H HK x Hx. rewrite (HK x Hx). exact (H x Hx). Qed.
(* the shape the engine leaves an inline check's obligation in, over a memory equal to m0 *)
Lemma vsl_obl : forall (W : world SEGS) (m0 m : word -> option byte) a, (forall x, m x = m0 x) ->
  range_addressable (rdW W m0) SHADOW_OFF a 1 -> range_addressable (rd_of SEGS (mrestrict (w_H W) m)) SHADOW_OFF a 1.
Proof using.
intros W m0 m a Hm H. change (rd_of SEGS (mrestrict (w_H W) m)) with (rdW W m).
apply (vsl_ra_kept (rdW W m0)); [exact H|]. intros x _. apply vsl_rd_eq. exact Hm.
Qed.
Lemma vsl_set_fs : forall S : astate, S = set_fs (st_fs S) S.
Proof using. intros S. destruct S. reflexivity. Qed.
(* a register a run left as an atom plus a constant *)
Lemma vsl_reg_off : forall E ss (ms : machine_state) (H : word -> bool) (r : bv 5) n z,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + z).
Proof using.
intros E ss ms H r n z HS Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs. cbn [sv_denot]. reflexivity.
Qed.
(* vs_regs from the registers a run kept *)
Lemma vsl_regs_keep : forall e (regs0 regs1 : bvmap 5 word), vs_regs e regs0 ->
  (forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ 22 <= r <= 27 ->
    getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) -> vs_regs e regs1.
Proof using.
intros e regs0 regs1 (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27) HK.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
- unfold spZ. change (getr regs1 2) with (getr regs1 (Z_to_bv 5 2)). rewrite (HK 2 ltac:(lia)). exact Hsp.
- change (getr regs1 3) with (getr regs1 (Z_to_bv 5 3)). rewrite (HK 3 ltac:(lia)). exact G3.
- change (getr regs1 4) with (getr regs1 (Z_to_bv 5 4)). rewrite (HK 4 ltac:(lia)). exact G4.
- change (getr regs1 8) with (getr regs1 (Z_to_bv 5 8)). rewrite (HK 8 ltac:(lia)). exact G8.
- change (getr regs1 9) with (getr regs1 (Z_to_bv 5 9)). rewrite (HK 9 ltac:(lia)). exact G9.
- change (getr regs1 18) with (getr regs1 (Z_to_bv 5 18)). rewrite (HK 18 ltac:(lia)). exact G18.
- change (getr regs1 19) with (getr regs1 (Z_to_bv 5 19)). rewrite (HK 19 ltac:(lia)). exact G19.
- change (getr regs1 22) with (getr regs1 (Z_to_bv 5 22)). rewrite (HK 22 ltac:(lia)). exact G22.
- intros r Hr. rewrite (HK r ltac:(lia)). exact (G27 r Hr).
Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* an object of segconf's code (sa_loc) lies below alloc_ceiling: a heap block, a side-stack frame or the image *)
Lemma vsl_loc_ceil : forall ly S W mem md q n, AR SEGS B ly S W mem md ->
  sa_loc SEGS B ly S q n -> 0 < n -> q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR HL Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hc & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & Hce & _ & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Q]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (_ & F1 & _). lia.
- destruct (HI (q + n - 1) ltac:(lia)) as (Himg & _ & _).
  pose proof (@pa_segs_low _ seg_listing PI _ Himg) as Hl. unfold kLowMemEnd in Hl. lia.
Qed.

(* vs_ctx0 at a later state of a stretch that wrote nothing *)
Lemma vsl_ctx0_next : forall e (regs0 regs1 : bvmap 5 word) mem0 mem1 md0 md1,
  vs_ctx0 B e regs0 mem0 md0 -> (forall x, mem1 x = mem0 x) ->
  ajournal SEGS B VS_STK (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) (e_W e) mem1 md1 0 ->
  vs_regs e regs1 -> vs_ctx0 B e regs1 mem1 md1.
Proof using.
intros e regs0 regs1 mem0 mem1 md0 md1 (_ & _ & HSL & HK & HP) Hm HJ HR.
unfold vs_ctx0, vs_ctxW. split; [exact HJ|]. split; [exact HR|]. split.
- apply (vs_slots_kept (rdW (e_W e) mem0)); [exact HSL|]. intros a _. apply vsl_rd_eq. exact Hm.
- split.
  + intros a Ha Hw Hn. rewrite (vsl_rd_eq (e_W e) mem0 mem1 Hm a). exact (HK a Ha Hw Hn).
  + intros a Ha. destruct (HP a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite Hm. exact Hb.
Qed.

(* one pass of the loop: from pass j to pass j + 1, to K2 at the NUL, or to KR at a byte that is no digit *)
Lemma vs_KL_step : vs_KR_stmt B gotw guard -> vs_K2_stmt B gotw guard ->
  forall j, vs_KL_stmt B gotw guard (S j) -> vs_KL_stmt B gotw guard j.
Proof using.
intros HKR HK2 j HKL e regs' mem' md' di HE HC Hdi Hdi0 Hlt Hdig R10 R11 R12 R13 R14 R15 R20.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (HJ & HR & HSL & HKP & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & _).
pose proof Hsadd as (Hq0 & Hq63 & _ & Hqra & _).
assert (HVS : VS_STK = 12352) by reflexivity.
unfold e_sp in *.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
pose proof (vsl_loc_ceil _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as Hsc.
assert (Hs47 : e_seg e + Z.of_nat (length (e_s e)) + 8 <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
(* the bytes of the segment and its NUL, as at the entry: they lie below alloc_ceiling, off the stack window *)
assert (HBY : forall i, (i <= length (e_s e))%nat ->
  rdW (e_W e) mem' (e_seg e + Z.of_nat i) = Some (nth i (e_s e) 0)).
{ intros i Hi. rewrite (HKP (e_seg e + Z.of_nat i) ltac:(lia) ltac:(lia) (fun x => x)).
  destruct Hstr as ((HZ & _) & _). rewrite (HZ i ltac:(rewrite length_app; cbn [length]; lia)).
  f_equal. destruct (Nat.eq_dec i (length (e_s e))) as [->|Hne].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
  - rewrite app_nth1 by lia. reflexivity. }
set (b := nth (S di + j) (e_s e) 0) in *.
set (b' := nth (S di + S j) (e_s e) 0).
assert (Rb : rdW (e_W e) mem' (e_seg e + Z.of_nat (S di + j)) = Some b) by (apply HBY; lia).
assert (Rb' : rdW (e_W e) mem' (e_seg e + Z.of_nat di + 2 + Z.of_nat j) = Some b').
{ replace (e_seg e + Z.of_nat di + 2 + Z.of_nat j) with (e_seg e + Z.of_nat (S di + S j)) by lia. apply HBY. lia. }
pose proof (vsl_byte _ _ _ _ Rb) as Hbr. pose proof (vsl_byte _ _ _ _ Rb') as Hbr'.
(* the shadow of dot[2 + j], what the check at 0x8a2c8 reads *)
assert (RA2 : range_addressable (rdW (e_W e) mem') SHADOW_OFF (e_seg e + Z.of_nat di + 2 + Z.of_nat j) 1).
{ apply (vsl_ra_kept (rdW (e_W e) (e_mem e))).
  - apply (range_addressable_sub _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [exact Hqra | lia | lia].
  - intros x Hx. unfold shadow_of_addr.
    assert (Hx8 : 0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    apply HKP; [unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | exact (fun f => f)]. }
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b']))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (E40 : ew E 40 = Z_to_bv 64 b') by (subst E; exact (vs_Ey regs' (e_regs e) [Z_to_bv 64 b'] 0 ltac:(lia))).
assert (U2 : bv_unsigned (ew E 2) = spZ regs') by (rewrite (EV 2%nat 2%bv eq_refl); reflexivity).
assert (U11 : bv_unsigned (ew E 11) = e_seg e + Z.of_nat di + 2 + Z.of_nat j)
  by (rewrite (EV 11%nat 11%bv eq_refl), R11; unfold w64; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = 9) by (rewrite (EV 12%nat 12%bv eq_refl), R12; reflexivity).
assert (U13 : bv_unsigned (ew E 13) = 2 ^ 64 - 1)
  by (rewrite (EV 13%nat 13%bv eq_refl), R13; unfold w64; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E 14) = e_seg e + Z.of_nat di + 1 + Z.of_nat j)
  by (rewrite (EV 14%nat 14%bv eq_refl), R14; unfold w64; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = b)
  by (rewrite (EV 15%nat 15%bv eq_refl), R15; unfold w64; apply unsigned_lit_small; lia).
(* the seeded state at KL, with the byte dot[2 + j] at a4 + 1 *)
assert (HS0 : st_ok_pi SEGS VAL E (vs_ssK VS_KL vsl_fs)
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_KL)) mem' (seg_rom SEGS)))).
{ apply vs_seedK.
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - lia.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - exact G22.
  - cbn [atoms_ok vsl_fs]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite U11, U12, U13, U14, E40, unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; first [exact I | lia]. }
assert (Rok : region_ok SEGS E (mrestrict (w_H (e_W e)) mem') vsl_r).
{ unfold region_ok, vsl_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U14. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (e_seg e + Z.of_nat di + 1 + Z.of_nat j) 1 1%N (SOff 40 0) b');
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  intros k Hk. assert (k = 0%nat) as -> by lia.
  lazymatch goal with |- context [Z_to_bv 8 (?f b' ?w 0%nat)] =>
    change (f b' w 0%nat) with ((Z.shiftr (b' mod 2 ^ (8 * Z.of_nat 1)) (8 * Z.of_nat 0)) mod 256) end.
  rewrite (vsl_le1 b') by lia.
  replace (e_seg e + Z.of_nat di + 1 + Z.of_nat j + 1 + Z.of_nat 0) with (e_seg e + Z.of_nat di + 2 + Z.of_nat j) by lia.
  apply vsl_mbyte. exact Rb'. }
assert (Rdj : all_disjoint E vsl_r (ss_mem (vs_ssK VS_KL vsl_fs))).
{ cbn [ss_mem vs_ssK all_disjoint]. unfold extent_disjoint.
  cbn [vsl_r vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U14, U2. split; [left; lia | exact I]. }
pose proof (st_ok_pi_add_region E _ _ vsl_r HS0 eq_refl Rok Rdj) as HS. clear HS0.
assert (SHOK : sh_ok SEGS vsl_Bx [] E (mrestrict (w_H (e_W e)) mem')) by (unfold sh_ok; apply Forall_nil).
assert (UB : U E vsl_Bx = SHADOW_OFF).
{ unfold vsl_Bx. apply U_atom; [rewrite (EV 22%nat 22%bv eq_refl), G22; reflexivity | unfold SHADOW_OFF; lia]. }
unfold vs_goal, vs_cfg.
(* 0x8a2bc `addi a5,a5,-48`, to the digit test 0x8a2c0 *)
paj_run_tok RUN HS HJ SHOK vsl_Bspan.
{ vs_awr_ro. }
vsl_mem HF. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK vsl_Bspan.
- (* 0x8a2c0 `bltu a2,a5` taken: dot[1 + j] is no digit; `li a0,0` and the epilogue *)
  assert (Hnd : SegModel.isdigit b = false).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom E 12%nat 9) in Hc
      by first [rewrite (EV 12%nat 12%bv eq_refl), R12; reflexivity | lia].
    rewrite (U_SOff E 15%nat (-48)), U15 in Hc. unfold zcanon, M64 in Hc.
    replace (b + -48) with (b - 48) in Hc by lia.
    rewrite (vs_digit_test b Hbr) in Hc. destruct (SegModel.isdigit b); [discriminate Hc | reflexivity]. }
  clear Hc.
  assert (Hvs : SegModel.vlan_split (e_s e) = None).
  { rewrite (vs_code_eq _ Hnul Hlen). apply (vs_none_nodigit _ di Hdi).
    destruct (forallb SegModel.isdigit (skipn (S di) (e_s e))) eqn:Hf; [|reflexivity].
    exfalso. rewrite forallb_forall in Hf.
    assert (Hin : In b (skipn (S di) (e_s e))).
    { unfold b. rewrite <- vs_tail_nth. apply nth_In. rewrite length_skipn. lia. }
    rewrite (Hf b Hin) in Hnd. discriminate. }
  paj_run_to_tok RUNTO HS HJ SHOK vsl_Bspan VS_KR.
  { vs_awr_ro. }
  vsl_mem HF. clear HF HFr HG.
  pmkst HS.
  apply (vs_exit_KR B gotw guard HKR e _ _ _ regs' mem' _ _ _ 0 HE HR HSL HJ).
  + vsl_keep HS EV.
  + intros a _. apply vsl_rd_eq. exact HM.
  + pose proof (st_ok_pi_restrict_reg (w_H (e_W e)) _ _ _ 10%bv HS) as F10.
    lazymatch type of F10 with _ = sv_denot _ (sr_get ?a ?r) =>
      let x := eval vm_compute in (sr_get a r) in change (sr_get a r) with x in F10 end.
    rewrite F10. reflexivity.
  + intros regs'' md'' H10''. unfold vs_Q. rewrite Hvs. split; [exact H10''|]. split; [exact I|]. split.
    * apply (vs_kept_step _ _ _ mem').
      -- exact (vs_kept_ctxW B e (fun _ => False) _ regs' mem' md' HC (fun a f => match f with end)).
      -- intros a _ _ _. apply vsl_rd_eq. exact HM.
    * split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs (e_S e)). apply vsl_set_fs.
- (* 0x8a2c0 not taken: dot[1 + j] is a digit *)
  assert (Hd : SegModel.isdigit b = true).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom E 12%nat 9) in Hc
      by first [rewrite (EV 12%nat 12%bv eq_refl), R12; reflexivity | lia].
    rewrite (U_SOff E 15%nat (-48)), U15 in Hc. unfold zcanon, M64 in Hc.
    replace (b + -48) with (b - 48) in Hc by lia.
    rewrite (vs_digit_test b Hbr) in Hc. destruct (SegModel.isdigit b); [reflexivity | discriminate Hc]. }
  clear Hc.
  (* 0x8a2c4 `beq a4,a3` -> unimp 0x8a3d8: refuted by decide_cond2 at the run, from the seed facts of a4 (atom 14
     in [0, 2^47 - 1]: dot + 1 + j < segment + length s + 8 <= 2^47 - 1, split_pre's amem_range segment
     (length s + 8)) and of a3 (atom 13 = 2^64 - 1): the ranges are apart, so the run answers "not taken".
     Then the check 0x8a2c8-0x8a2d4 of the load1 of a1 = dot + 2 + j (its obligation below), `addi a4,a4,1`,
     `lbu a5,0(a4)` from the seeded byte, `addi a1,a1,1`, to `beqz a5`. *)
  paj_run_tok RUN HS HJ SHOK vsl_Bspan.
  { (* the check of the load1 at a1 = dot + 2 + j: the segment's addressable range (split_pre's sa_addr) *)
    rewrite UB, (U_atom E 11%nat (e_seg e + Z.of_nat di + 2 + Z.of_nat j))
      by first [rewrite (EV 11%nat 11%bv eq_refl), R11; reflexivity | lia].
    apply (vsl_obl (e_W e) mem'); [exact HM | exact RA2]. }
  { vs_awr_ro. }
  vsl_mem HF. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK vsl_Bspan.
  + (* 0x8a2e4 `beqz a5` taken: dot[2 + j] is the NUL, the tail is all digits: K2 *)
    assert (Hb'0 : b' = 0).
    { rewrite branch_eq_U in Hc. rewrite (U_atom _ 40%nat b') in Hc
        by first [repeat (rewrite ew_ewset_other by lia); exact E40 | lia].
      rewrite U_lit in Hc by lia. apply Z.eqb_eq. exact Hc. }
    clear Hc.
    assert (Hend : (S di + S j = length (e_s e))%nat).
    { destruct (Nat.lt_ge_cases (S di + S j) (length (e_s e))) as [Hl|Hl]; [|lia]. exfalso. apply Hnul.
      rewrite <- Hb'0. unfold b'. apply nth_In. exact Hl. }
    assert (Htl : length (vs_tail e di) = S j) by (unfold vs_tail; rewrite length_skipn; lia).
    assert (Hdg : forallb SegModel.isdigit (vs_tail e di) = true).
    { assert (Hfa : firstn (S j) (vs_tail e di) = vs_tail e di) by (apply firstn_all2; lia).
      rewrite <- Hfa.
      rewrite vs_forallb_firstn_S by lia. rewrite Hdig. unfold vs_tail. rewrite vs_tail_nth.
      change (nth (S di + j) (e_s e) 0) with b. rewrite Hd. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK vsl_Bspan VS_K2.
    { vs_awr_ro. }
    vsl_mem HF. clear HF HFr HG.
    pmkst HS.
    apply (HK2 e _ _ _ di HE).
    * apply (vsl_ctx0_next e regs' _ mem' _ md' _ HC HM HJ). apply (vsl_regs_keep e regs' _ HR). vsl_keep HS EV.
    * exact Hdi.
    * exact Hdi0.
    * intros Hn. rewrite Hn in Htl. discriminate.
    * exact Hdg.
    * rewrite (vs_reg_atom _ _ _ _ regs' 10%nat 10%bv HS ltac:(repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity)
        ltac:(vm_compute; reflexivity)). exact R10.
    * rewrite (vs_reg_atom _ _ _ _ regs' 20%nat 20%bv HS ltac:(repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity)
        ltac:(vm_compute; reflexivity)). exact R20.
  + (* 0x8a2e4 not taken: dot[2 + j] is a digit candidate; 0x8a2e8 `j 0x8a2bc`: KL, pass j + 1 *)
    assert (Hb'0 : b' <> 0).
    { rewrite branch_eq_U in Hc. rewrite (U_atom _ 40%nat b') in Hc
        by first [repeat (rewrite ew_ewset_other by lia); exact E40 | lia].
      rewrite U_lit in Hc by lia. apply Z.eqb_neq. exact Hc. }
    clear Hc.
    assert (Hlt' : (S di + S j < length (e_s e))%nat).
    { destruct (Nat.eq_dec (S di + S j) (length (e_s e))) as [Ei|Ei]; [|lia]. exfalso. apply Hb'0.
      unfold b'. rewrite Ei. apply nth_overflow. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK vsl_Bspan VS_KL.
    { vs_awr_ro. }
    vsl_mem HF. clear HF HFr HG.
    pmkst HS.
    apply (HKL e _ _ _ di HE).
    * apply (vsl_ctx0_next e regs' _ mem' _ md' _ HC HM HJ). apply (vsl_regs_keep e regs' _ HR). vsl_keep HS EV.
    * exact Hdi.
    * exact Hdi0.
    * exact Hlt'.
    * rewrite vs_forallb_firstn_S by (unfold vs_tail; rewrite length_skipn; lia). rewrite Hdig.
      unfold vs_tail. rewrite vs_tail_nth. change (nth (S di + j) (e_s e) 0) with b. rewrite Hd. reflexivity.
    * rewrite (vs_reg_atom _ _ _ _ regs' 10%nat 10%bv HS ltac:(repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity)
        ltac:(vm_compute; reflexivity)). exact R10.
    * rewrite (vsl_reg_off _ _ _ _ 11%bv 11%nat 1 HS ltac:(vm_compute; reflexivity)).
      rewrite !ew_ewset_other by lia. rewrite U11. unfold w64. f_equal. lia.
    * rewrite (vs_reg_atom _ _ _ _ regs' 12%nat 12%bv HS ltac:(repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity)
        ltac:(vm_compute; reflexivity)). exact R12.
    * rewrite (vs_reg_atom _ _ _ _ regs' 13%nat 13%bv HS ltac:(repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity)
        ltac:(vm_compute; reflexivity)). exact R13.
    * rewrite (vsl_reg_off _ _ _ _ 14%bv 14%nat 1 HS ltac:(vm_compute; reflexivity)).
      rewrite !ew_ewset_other by lia. rewrite U14. unfold w64. f_equal. lia.
    * rewrite (vsl_reg_off _ _ _ _ 15%bv 40%nat 0 HS ltac:(vm_compute; reflexivity)).
      rewrite !ew_ewset_other by lia. rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * rewrite (vs_reg_atom _ _ _ _ regs' 20%nat 20%bv HS ltac:(repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity)
        ltac:(vm_compute; reflexivity)). exact R20.
Qed.

Lemma vs_KL : vs_KR_stmt B gotw guard -> vs_K2_stmt B gotw guard -> forall j, vs_KL_stmt B gotw guard j.
Proof using.
intros HKR HK2.
assert (IND : forall k j, (15 <= j + k)%nat -> vs_KL_stmt B gotw guard j).
{ induction k as [|k IH]; intros j Hk.
  - intros e regs' mem' md' di HE _ _ _ Hlt. exfalso.
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _). destruct HSP as (_ & _ & Hlen & _). lia.
  - apply (vs_KL_step HKR HK2 j). apply IH. lia. }
intros j. apply (IND 15%nat j). lia.
Qed.
End e.
End f.
End d.
