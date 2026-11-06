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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 414 of its 466 lines of code are new or changed and 401 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, m_file at 0x86140): segment S_MF_LONGP of its walk
   (LONG 0x863d4 -> TAIL 0x86820), part 2: the blank skip, LONG from LP_CALLPX (lib/B/Prog/mf_longp_1.v). A walk lane of the image-B m_file-family owner's G2B. Adapted from the image-A m_file-family lane's image-A walk (commit
   93220999e732, its statement lib/A/Prog/m_file_s_long_d.v; the loop in the form of lib/A/Prog/m_file_s_krole_w.v,
   a working branch) at image B's numbers.
   - lp_iter: one pass of the blank skip from LP_HEAD 0x863e0 with k blank bytes behind the cursor f = p + k: the
     instrumented check of *f (a load of the shadow byte at (f >> 3) + s2 and a compare; the token run turns it into
     the obligation `f is addressable', which mf_loop's sa_addr gives at the LONG state's memory, kept outside the cur
     cell); *f > 0x20 or bit *f of the blank mask clear: the first non-blank byte, its check again at 0x867ec, cur =
     NULL when it is '[' (0x867f4-0x8680c, the store into 136(s1)), LP_CALLPX at 0x86810; *f blank: f + 1, back to
     LP_HEAD (k + 1 < |line|) or, at the line's end, LP_CALLPX with cur unchanged.
   - lp_loop_all: every k by induction on n - k (k < |line| <= |rest| <= n).
   - lp_long_of_callpx: LONG 0x863d4: s5 = the next line's address, the test p >= e (never taken: |line| >= 512),
     a1 = s10, LP_HEAD at k = 0.
   The light state (mf_longp_1.v lp_ss): every register its own atom, the facts the token engine asks (s2 = SHADOW_OFF,
   s1 in [2^46, 2^47] and 32-aligned, the cursor in [4096, 2^47 - 2^23]), the byte at s10 (read-only) and the cur cell
   (writable). No UBSan trap branch lies in the segment. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k mf_longp_1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the state's form, computed *)
Ltac lp_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* the registers a run of the blank skip does not touch: mf_regs_at's eleven, s4, s5, s11; and a0, a6 on the way
   back to the head; s10 instead of s5 on the run from LONG *)
Definition LP_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Definition LP_KEPTL : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 10; 16]%bv.
Definition LP_KEPT0 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27; 10; 16]%bv.

(* ===================================== pure facts of the runs ===================================== *)
Lemma lp_U_at : forall E0 En n x, env_agree 34 E0 En -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  U En (SOff n 0) = x.
Proof. intros E0 En n x HA Hn Hx Hr. apply U_atom; [rewrite (proj1 HA n Hn); exact Hx | exact Hr]. Qed.
Lemma lp_U_at1 : forall E0 En n x, env_agree 34 E0 En -> (n < 34)%nat -> ew E0 n = Z_to_bv 64 x -> 0 <= x ->
  x + 1 < 2 ^ 64 -> U En (SOff n 1) = x + 1.
Proof. intros E0 En n x HA Hn Hx H0 H1. apply U_atom_off; [rewrite (proj1 HA n Hn); exact Hx | lia | lia]. Qed.
(* the byte loaded by `lbu` *)
Lemma lp_Ub : forall E0 En b, env_agree 34 E0 En -> ew E0 32 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U En (SExt false 8 (SOff 32 0)) = b.
Proof.
intros E0 En b HA Hb Hr. rewrite U_zext, (lp_U_at E0 En 32 b HA ltac:(lia) Hb ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
(* the blank mask's bit b, as `srl` computes it *)
Lemma lp_mask_U : forall b, 0 <= b <= 32 -> Z.land (zcanon (zalu_raw 63 64 ALU_SRL MF_BLANK b)) 1 = if blank b then 1 else 0.
Proof.
intros b Hb. replace b with (Z.of_nat (Z.to_nat b)) by lia. assert (Hn : (Z.to_nat b <= 32)%nat) by lia.
generalize (Z.to_nat b) Hn. clear. intros n Hn.
do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
(* 0x863f8-0x863fc: (s3 >> *f) & 1 *)
Lemma lp_Umask : forall E0 En b, env_agree 34 E0 En -> ew E0 32 = Z_to_bv 64 b -> 0 <= b <= 32 ->
  ew E0 19 = Z_to_bv 64 MF_BLANK ->
  U En (SAlu ALU_AND (SAlu ALU_SRL (SOff 19 0) (SExt false 8 (SOff 32 0))) (SLit 1)) = if blank b then 1 else 0.
Proof.
intros E0 En b HA Hb Hr H19. rewrite U_and_lit by lia. rewrite U_SAlu.
rewrite (lp_U_at E0 En 19 MF_BLANK HA ltac:(lia) H19 ltac:(unfold MF_BLANK; lia)), (lp_Ub E0 En b HA Hb ltac:(lia)).
apply lp_mask_U. exact Hr.
Qed.
(* 0x867f4-0x86808: cur becomes NULL when the byte *f is '[', else stays *)
Lemma lp_Ucur : forall E0 En b cp, env_agree 34 E0 En -> ew E0 32 = Z_to_bv 64 b -> 0 <= b < 256 ->
  ew E0 33 = Z_to_bv 64 cp -> 0 <= cp < 2 ^ 64 ->
  U En (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SExt false 8 (SOff 32 0)) (SLit (-91))) (SLit 1))
    (SLit (-1))) (SOff 33 0)) = if b =? 91 then 0 else cp.
Proof.
intros E0 En b cp HA Hb Hr Hc Hcr. rewrite !U_SAlu.
rewrite (lp_Ub E0 En b HA Hb Hr), (lp_U_at E0 En 33 cp HA ltac:(lia) Hc Hcr), !U_SLit. cbn [zalu_raw].
destruct (Z.eqb_spec b 91) as [-> | Hne].
- vm_compute. reflexivity.
- assert (E1 : (zcanon (b + zcanon (-91)) <? zcanon 1) = false).
  { apply Z.ltb_ge. change (zcanon 1) with 1. unfold zcanon, M64. rewrite Zplus_mod_idemp_r.
    destruct (Z_lt_ge_dec b 91) as [Hl | Hg].
    - rewrite <- (Z.mod_unique (b + -91) (2 ^ 64) (-1) (b + -91 + 2 ^ 64)) by lia. lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite E1. replace (zcanon (zcanon 0 + zcanon (-1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma lp_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree 34 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run whose write windows lie in the cur cell keeps every other byte *)
Lemma lp_keep_step : forall (W : world SEGS) Ex rs m0 m1 memc s1,
  frame_of Ex rs (mrestrict (w_H W) m0) (mrestrict (w_H W) m1) ->
  (forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= x < base_val Ex b + whi ->
   s1 + 136 <= x < s1 + 144) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW W m0 a = rdW W memc a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW W m1 a = rdW W memc a.
Proof.
intros W Ex rs m0 m1 memc s1 HF Hw K a Ha Hs. rewrite <- (K a Ha Hs).
exact (kept_of_frame Ex rs (w_H W) m0 m1 (fun a => s1 + 136 <= a < s1 + 144) HF Hw a Ha Hs).
Qed.
(* the text left's addressability at a memory that agrees with the LONG state's off the cur cell *)
Lemma lp_pra : forall (W : world SEGS) m memc s1 p n,
  range_addressable (rdW W memc) SHADOW_OFF p n ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW W m a = rdW W memc a) ->
  0 <= p -> p + n <= 2 ^ 47 -> 2 ^ 46 <= s1 ->
  range_addressable (rdW W m) SHADOW_OFF p n.
Proof.
intros W m memc s1 p n HRA K H0 H1 H2 x Hx. destruct (HRA x Hx) as (sx & Hsx & Hok). exists sx. split; [|exact Hok].
unfold shadow_of_addr in *. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
rewrite K; [exact Hsx | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia].
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a run: the environment agrees with the seed's E0 below 34 (HAE), the model abbreviated *)
Ltac lp_after E0 HAE :=
  try (let mdv := fresh "mdv" in set (mdv := with_vm_backing _ _ _) in *; clearbody mdv);
  lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
    let HAEn := fresh "HAEn" in assert (HAEn : env_agree 34 E0 En) by (env_agree_chain HAE);
    clear HAE; rename HAEn into HAE end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end.
(* after a run, before lp_after: the bytes off the cur cell still the LONG state's *)
Ltac lp_keepk Wc memc s1 HAE U9 KEEP :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H Wc) ?m0) (mrestrict (w_H Wc) ?m1) |- _ =>
    let KEEPn := fresh "KEEPn" in
    assert (KEEPn : forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 136 <= a < s1 + 144) -> rdW Wc m1 a = rdW Wc memc a);
    [ apply (lp_keep_step Wc Ex rs m0 m1 memc s1 HFr); [|exact KEEP];
      intros bw wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [ injection Hq as <- <- <-; cbn [base_val] in Hr;
          first [ lia | rewrite U9 in Hr; lia | rewrite (proj1 HAE 9%nat ltac:(lia)), U9 in Hr; lia ] |]);
      destruct Hinw
    | clear KEEP; rename KEEPn into KEEP ] end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* a run's side goals: the token obligations (the cursor addressable) and the writes (the cur cell) *)
Ltac lp_side v s1 HAE U9 E11 E18 HSTK PRA :=
  lazymatch goal with
  | |- SRr _ _ _ _ => idtac
  | |- range_addressable _ (U ?Ex _) (U ?Ex (SOff 11 0)) 1 =>
      cbn [ms_mem mkst];
      rewrite (lp_U_at _ Ex 11 _ HAE ltac:(lia) E11 ltac:(lia));
      eapply (obl_of_range SEGS _ _ Ex lp_Bx _ 1 _ _ PRA
        (lp_U_at _ Ex 18 SHADOW_OFF HAE ltac:(lia) E18 ltac:(unfold SHADOW_OFF; lia))); lia
  | |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs';
      apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
      eapply awr_ok_cons_stack_off with (n := 9%nat) (d := s1 - mv_sp v);
        [ reflexivity
        | first [rewrite U9 | rewrite (proj1 HAE 9%nat ltac:(lia)), U9]; lia
        | cbn [YP09.r_wlo]; rewrite HSTK; lia
        | cbn [YP09.r_whi]; lia
        | apply awr_ok_nil ]
  end.

(* one pass of the blank skip *)
Lemma lp_iter : forall n k, LP_CALLPX_stmt B n -> LP_LOOP_stmt B n (S k) -> LP_LOOP_stmt B n k.
Proof.
intros n k CALLP NEXT. unfold LP_LOOP_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest memk mdk CX LS FRM CORE CELLS RA Hn Hne LP Hlong MOD
  Hk Hbl R26 R11 R10 R21 R16 R27 R20 MEM.
pose proof MEM as (HJk & KEEP & VCUR).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
destruct (lp_txt_bounds B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LP) as (Tp0 & Tp1).
pose proof (lp_line_len rest) as HLL.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
set (s1 := mf_s1 (mv_sp v)) in *.
set (L := length (mf_line rest)) in *.
pose proof LP as (_ & _ & _ & ((Lzs & Lnz) & _) & (A0 & A1 & A2 & ARA & _) & Hcok & _).
assert (Hkr : (k < length rest)%nat) by lia.
assert (Hb : rdW Wc memc (p + Z.of_nat k) = Some (nth k rest 0)).
{ rewrite (Lzs k) by (rewrite length_app; cbn [length]; lia). rewrite app_nth1 by lia. reflexivity. }
assert (HbL : nth k (mf_line rest) 0 = nth k rest 0) by (apply lp_line_nth; exact Hk).
set (b := nth k rest 0) in *.
assert (Hbk : rdW Wc memk (p + Z.of_nat k) = Some b) by (rewrite KEEP; [exact Hb | lia | lia]).
destruct (aview_byte SEGS (w_H Wc) memk _ b Hbk) as (bb & _ & _ & Hb256).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcok) as Hcp.
set (cp := mf_cur_ptr (mv_c v) cur) in *.
pose proof HJk as (HARk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hwr : forall a, s1 + 136 <= a < s1 + 144 -> writable_at SEGS (mrestrict (w_H Wc) memk) a).
{ intros a Ha. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK. lia. }
pose proof (lp_seed Wc regs1 memk LP_HEAD (p + Z.of_nat k) s1 b cp R26 R9
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb256 Hcp (mf_val1_of_aview (w_H Wc) memk _ b Hbk) VCUR Hwr) as HS.
set (E0 := lp_E regs1 b cp) in HS.
assert (E32 : ew E0 32 = Z_to_bv 64 b) by apply lp_ew32.
assert (E33 : ew E0 33 = Z_to_bv 64 cp) by apply lp_ew33.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E0 n0 = getr regs1 r)
  by (intros; apply lp_ew_reg; assumption).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, lp_E; apply Eimg_env).
pose proof (lp_env_agree regs1 b cp) as HA0. fold E0 in HA0.
assert (U9 : bv_unsigned (ew E0 9) = s1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply mf_w64_u; lia).
assert (E11 : ew E0 11 = Z_to_bv 64 (p + Z.of_nat k)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (U11 : bv_unsigned (ew E0 11) = p + Z.of_nat k) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E26 : ew E0 26 = Z_to_bv 64 (p + Z.of_nat k)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (U26 : bv_unsigned (ew E0 26) = p + Z.of_nat k) by (rewrite E26; apply unsigned_lit_small; lia).
assert (E10 : ew E0 10 = Z_to_bv 64 (p + Z.of_nat L)) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E16 : ew E0 16 = Z_to_bv 64 32) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E19 : ew E0 19 = Z_to_bv 64 MF_BLANK) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E18 : ew E0 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E0 18) = SHADOW_OFF) by (rewrite E18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
clearbody E0.
apply (st_ok_pi_add_fact E0 _ _ 11 (HPTR 0)) in HS;
  [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U11; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
apply (st_ok_pi_add_fact E0 _ _ 9 (mkAF (2 ^ 46) (2 ^ 47) 5)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 5) with 32; lia].
apply (st_ok_pi_add_fact E0 _ _ 18 (mkAF SHADOW_OFF SHADOW_OFF 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18; change (2 ^ 0) with 1; rewrite Z.mod_1_r;
     unfold SHADOW_OFF; lia].
lp_norm HS.
assert (SHOK : sh_ok SEGS lp_Bx [] E0 (mrestrict (w_H Wc) memk)) by constructor.
pose proof (env_agree_refl 34 E0) as HAE.
pose proof (lp_pra Wc memk memc s1 p _ ARA KEEP ltac:(lia) ltac:(lia) ltac:(lia)) as PRA.
unfold mf_at.
(* the check of *f, the byte, up to `bltu a6,a3` *)
paj_run_tok RUN HS HJk SHOK Bspan.
all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
lp_keepk Wc memc s1 HAE U9 KEEP.
lp_after E0 HAE.
clear PRA.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ =>
  pose proof (lp_pra Wc (ms_mem m) memc s1 p _ ARA KEEP ltac:(lia) ltac:(lia) ltac:(lia)) as PRA end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* *f > 0x20: not blank *)
  rewrite branch_ltu_U, (lp_U_at E0 _ 16 32 HAE ltac:(lia) E16 ltac:(lia)), (lp_Ub E0 _ b HAE E32 Hb256) in Hc.
  apply Z.ltb_lt in Hc. pose proof (lp_blank_gt b Hc) as Hnb. clear Hc.
  assert (MOD' : mf_fin (m_refuse mcc (line + 1) false, if b =? 91 then None else cur) line rest = mf_final v).
  { rewrite <- MOD. rewrite (lp_line_long mcc cur (line + 1) (mf_line rest) Hlong).
    rewrite (lp_drop_k (mf_line rest) k Hk Hbl) by (rewrite HbL; exact Hnb). rewrite HbL. reflexivity. }
  (* 0x867ec: the check of *f again, cur = NULL on '[', the store into 136(s1), up to 0x86810 *)
  paj_run_to_tok RUNTO HS HJk SHOK Bspan LP_CALLP.
  all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
  lp_keepk Wc memc s1 HAE U9 KEEP.
  lp_after E0 HAE.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?m) |- _ =>
    pose proof (st_ok_pi_region_nth En _ _ 1 _ HS eq_refl) as HR;
    assert (VCUR' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem m)) (s1 + 136) 8
      (mf_cur_ptr (mv_c v) (if b =? 91 then None else cur)));
    [ lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
        eapply (field_of_region En _ nb s1 cs lo hi wlo whi 136 8%N _ _ HR);
        [ rewrite (proj1 HAE 9%nat ltac:(lia)); exact U9
        | cbn [In]; left; reflexivity
        | rewrite denot_lit_U; f_equal; rewrite (lp_Ucur E0 En b cp HAE E32 Hb256 E33 Hcp);
          destruct (b =? 91); reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (b =? 91); [cbn [mf_cur_ptr]; lia | exact Hcp]
        | cbn; lia ] end
    | ] end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?j)) _ _) _) _ =>
    change (Z_to_bv 64 (BASE + j)) with (Z_to_bv 64 (BASE + LP_CALLP)) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
    assert (RA' : mf_regs_at B v lyc pos rg) by
      (apply (mf_regs_at_of B v lyc pos regs1 _ RA); apply HK; cbv [LP_KEPT In]; tauto) end.
  apply (CALLP v lyc Sc Wc _ memc mdc pos mcc cur (if b =? 91 then None else cur) line p rest _ _ CX LS FRM CORE CELLS
    RA' Hn Hne LP Hlong ltac:(destruct (b =? 91); [right | left]; reflexivity) MOD').
  -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R21.
  -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R27.
  -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R20.
  -- exact (conj HJk (conj KEEP VCUR')).
- (* *f <= 0x20: the blank mask *)
  rewrite branch_ltu_U, (lp_U_at E0 _ 16 32 HAE ltac:(lia) E16 ltac:(lia)), (lp_Ub E0 _ b HAE E32 Hb256) in Hc.
  apply Z.ltb_ge in Hc. rename Hc into Hb32.
  paj_run_tok RUN HS HJk SHOK Bspan.
  all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
  lp_keepk Wc memc s1 HAE U9 KEEP.
  lp_after E0 HAE.
  clear PRA.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ =>
    pose proof (lp_pra Wc (ms_mem m) memc s1 p _ ARA KEEP ltac:(lia) ltac:(lia) ltac:(lia)) as PRA end.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the bit is clear: not blank *)
    rewrite branch_eq_U, (lp_Umask E0 _ b HAE E32 ltac:(lia) E19), U_SLit in Hc.
    assert (Hnb : blank b = false) by (destruct (blank b); [vm_compute in Hc; discriminate Hc | reflexivity]). clear Hc.
    assert (MOD' : mf_fin (m_refuse mcc (line + 1) false, if b =? 91 then None else cur) line rest = mf_final v).
    { rewrite <- MOD. rewrite (lp_line_long mcc cur (line + 1) (mf_line rest) Hlong).
      rewrite (lp_drop_k (mf_line rest) k Hk Hbl) by (rewrite HbL; exact Hnb). rewrite HbL. reflexivity. }
    (* 0x867ec: the check of *f again, cur = NULL on '[', the store into 136(s1), up to 0x86810 *)
    paj_run_to_tok RUNTO HS HJk SHOK Bspan LP_CALLP.
    all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
    lp_keepk Wc memc s1 HAE U9 KEEP.
    lp_after E0 HAE.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?m) |- _ =>
      pose proof (st_ok_pi_region_nth En _ _ 1 _ HS eq_refl) as HR;
      assert (VCUR' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem m)) (s1 + 136) 8
        (mf_cur_ptr (mv_c v) (if b =? 91 then None else cur)));
      [ lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
          eapply (field_of_region En _ nb s1 cs lo hi wlo whi 136 8%N _ _ HR);
          [ rewrite (proj1 HAE 9%nat ltac:(lia)); exact U9
          | cbn [In]; left; reflexivity
          | rewrite denot_lit_U; f_equal; rewrite (lp_Ucur E0 En b cp HAE E32 Hb256 E33 Hcp);
            destruct (b =? 91); reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct (b =? 91); [cbn [mf_cur_ptr]; lia | exact Hcp]
          | cbn; lia ] end
      | ] end.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?j)) _ _) _) _ =>
      change (Z_to_bv 64 (BASE + j)) with (Z_to_bv 64 (BASE + LP_CALLP)) end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
      assert (RA' : mf_regs_at B v lyc pos rg) by
        (apply (mf_regs_at_of B v lyc pos regs1 _ RA); apply HK; cbv [LP_KEPT In]; tauto) end.
    apply (CALLP v lyc Sc Wc _ memc mdc pos mcc cur (if b =? 91 then None else cur) line p rest _ _ CX LS FRM CORE CELLS
      RA' Hn Hne LP Hlong ltac:(destruct (b =? 91); [right | left]; reflexivity) MOD').
    -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R21.
    -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R27.
    -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R20.
    -- exact (conj HJk (conj KEEP VCUR')).
  + (* blank: the next byte *)
    rewrite branch_eq_U, (lp_Umask E0 _ b HAE E32 ltac:(lia) E19), U_SLit in Hc.
    assert (Hbk1 : blank b = true) by (destruct (blank b); [reflexivity | vm_compute in Hc; discriminate Hc]). clear Hc.
    paj_run_tok RUN HS HJk SHOK Bspan.
    all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
    lp_keepk Wc memc s1 HAE U9 KEEP.
    lp_after E0 HAE.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* f + 1 is not the line's end: LP_HEAD at k + 1 *)
      rewrite branch_ne_U, (lp_U_at1 E0 _ 26 (p + Z.of_nat k) HAE ltac:(lia) E26 ltac:(lia) ltac:(lia)),
        (lp_U_at E0 _ 10 (p + Z.of_nat L) HAE ltac:(lia) E10 ltac:(lia)) in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJk SHOK Bspan LP_HEAD.
      all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
      lp_keepk Wc memc s1 HAE U9 KEEP.
      lp_after E0 HAE.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ LP_KEPTL HS (lp_ag32 _ _ _ _ HA0 HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      prreg HS (26%bv : bv 5) Q26. prreg HS (11%bv : bv 5) Q11.
      lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?m) |- _ =>
        pose proof (st_ok_pi_region_nth En _ _ 1 _ HS eq_refl) as HR;
        assert (VCUR' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem m)) (s1 + 136) 8 cp);
        [ lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
            eapply (field_of_region En _ nb s1 cs lo hi wlo whi 136 8%N _ cp HR);
            [ rewrite (proj1 HAE 9%nat ltac:(lia)); exact U9
            | cbn [In]; left; reflexivity
            | rewrite denot_lit_U; f_equal; exact (lp_U_at E0 En 33 cp HAE ltac:(lia) E33 Hcp)
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hcp
            | cbn; lia ] end
        | ] end.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?j)) _ _) _) _ =>
        change (Z_to_bv 64 (BASE + j)) with (Z_to_bv 64 (BASE + LP_HEAD)) end.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
        assert (RA' : mf_regs_at B v lyc pos rg) by
          (apply (mf_regs_at_of B v lyc pos regs1 _ RA); apply HK; cbv [LP_KEPTL In]; tauto) end.
      apply (NEXT v lyc Sc Wc _ memc mdc pos mcc cur line p rest _ _ CX LS FRM CORE CELLS RA' Hn Hne LP Hlong MOD).
      -- lia.
      -- intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hjk]; [rewrite HbL; exact Hbk1 | apply Hbl; lia].
      -- rewrite Q26, U26. unfold w64. f_equal. lia.
      -- rewrite Q11, U11. unfold w64. f_equal. lia.
      -- rewrite HK by (cbv [LP_KEPTL In]; tauto). exact R10.
      -- rewrite HK by (cbv [LP_KEPTL In]; tauto). exact R21.
      -- rewrite HK by (cbv [LP_KEPTL In]; tauto). exact R16.
      -- rewrite HK by (cbv [LP_KEPTL In]; tauto). exact R27.
      -- rewrite HK by (cbv [LP_KEPTL In]; tauto). exact R20.
      -- exact (conj HJk (conj KEEP VCUR')).
    * (* f + 1 is the line's end: every byte blank, LP_CALLPX with cur *)
      rewrite branch_ne_U, (lp_U_at1 E0 _ 26 (p + Z.of_nat k) HAE ltac:(lia) E26 ltac:(lia) ltac:(lia)),
        (lp_U_at E0 _ 10 (p + Z.of_nat L) HAE ltac:(lia) E10 ltac:(lia)) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc.
      assert (Hall : forall j, (j < length (mf_line rest))%nat -> blank (nth j (mf_line rest) 0) = true).
      { intros j Hj. destruct (Nat.eq_dec j k) as [-> | Hjk]; [rewrite HbL; exact Hbk1 | apply Hbl; lia]. }
      assert (MOD' : mf_fin (m_refuse mcc (line + 1) false, cur) line rest = mf_final v).
      { rewrite <- MOD. rewrite (lp_line_long mcc cur (line + 1) (mf_line rest) Hlong).
        rewrite (lp_drop_all (mf_line rest) Hall). reflexivity. }
      paj_run_to_tok RUNTO HS HJk SHOK Bspan LP_CALLP.
      all: lp_side v s1 HAE U9 E11 E18 HSTK PRA.
      lp_keepk Wc memc s1 HAE U9 KEEP.
      lp_after E0 HAE.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ LP_KEPT HS (lp_ag32 _ _ _ _ HA0 HAE)
        ltac:(vm_compute; reflexivity)) as HK.
      cbn [ms_regs restrict] in HK.
      lazymatch goal with HS : st_ok_pi _ _ ?En _ (restrict _ ?m) |- _ =>
        pose proof (st_ok_pi_region_nth En _ _ 1 _ HS eq_refl) as HR;
        assert (VCUR' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem m)) (s1 + 136) 8 cp);
        [ lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
            eapply (field_of_region En _ nb s1 cs lo hi wlo whi 136 8%N _ cp HR);
            [ rewrite (proj1 HAE 9%nat ltac:(lia)); exact U9
            | cbn [In]; left; reflexivity
            | rewrite denot_lit_U; f_equal; exact (lp_U_at E0 En 33 cp HAE ltac:(lia) E33 Hcp)
            | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hcp
            | cbn; lia ] end
        | ] end.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?j)) _ _) _) _ =>
        change (Z_to_bv 64 (BASE + j)) with (Z_to_bv 64 (BASE + LP_CALLP)) end.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
        assert (RA' : mf_regs_at B v lyc pos rg) by
          (apply (mf_regs_at_of B v lyc pos regs1 _ RA); apply HK; cbv [LP_KEPT In]; tauto) end.
      apply (CALLP v lyc Sc Wc _ memc mdc pos mcc cur cur line p rest _ _ CX LS FRM CORE CELLS RA' Hn Hne LP Hlong
        (or_introl eq_refl) MOD').
      -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R21.
      -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R27.
      -- rewrite HK by (cbv [LP_KEPT In]; tauto). exact R20.
      -- exact (conj HJk (conj KEEP VCUR')).
Qed.

(* every pass, by induction on n - k *)
Lemma lp_loop_all : forall n, LP_CALLPX_stmt B n -> forall m k, (n <= k + m)%nat -> LP_LOOP_stmt B n k.
Proof.
intros n CALLP m. induction m as [|m IH]; intros k Hm.
- unfold LP_LOOP_stmt. intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest memk mdk CX LS FRM CORE CELLS RA
    Hn Hne LP Hlong MOD Hk. pose proof (lp_line_len rest). lia.
- apply (lp_iter n k CALLP). apply IH. lia.
Qed.

(* LONG 0x863d4: s5 = the next line's address, p < e, a1 = s10, LP_HEAD at k = 0 *)
Lemma lp_long_of_callpx : forall n, LP_CALLPX_stmt B n -> MF_LONG_stmt B n.
Proof.
intros n CALLP. pose proof (lp_loop_all n CALLP n 0 ltac:(lia)) as LOOP0. unfold MF_LONG_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA Hn Hne LP Hlong MOD
  R26 R10 R12 R16 R27 R20.
pose proof CORE as (HJ & _).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C136 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & Hs32 & _).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
destruct (lp_txt_bounds B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc mcc cur line p rest CX CORE LP) as (Tp0 & Tp1).
pose proof (lp_line_len rest) as HLL.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (lp_seed0 Wc regs1 memc MF_LONG 0 0) as HS.
assert (SHOK : sh_ok SEGS lp_Bx [] (lp_E regs1 0 0) (mrestrict (w_H Wc) memc)) by constructor.
assert (HEI : img_env VAL A_LIM (lp_E regs1 0 0)) by (unfold lp_E; apply Eimg_env).
assert (E26 : ew (lp_E regs1 0 0) 26 = Z_to_bv 64 p) by (rewrite (lp_ew_reg _ _ _ 26 26%bv eq_refl); exact R26).
assert (E10 : ew (lp_E regs1 0 0) 10 = Z_to_bv 64 (p + Z.of_nat (length (mf_line rest))))
  by (rewrite (lp_ew_reg _ _ _ 10 10%bv eq_refl); exact R10).
unfold mf_at.
(* 0x863d4 `mv s5,a2`, up to `bgeu s10,a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* p >= e: never *)
  exfalso. rewrite branch_geu_U, (U_atom _ 26 p E26 ltac:(lia)), (U_atom _ 10 _ E10 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.ltb_ge in Hc. lia.
- clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan LP_HEAD.
  { apply awr_ok_nil. }
  (* both runs wrote nothing (no region): every byte as at LONG *)
  assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. transitivity (rdW Wc (ms_mem ms) a).
    - refine (kept_of_frame _ _ (w_H Wc) _ _ (fun _ => False) HFr0 _ a Ha (fun x => x)).
      intros bw wlo whi x Hinw Hr. vm_compute in Hinw. destruct Hinw.
    - refine (kept_of_frame _ _ (w_H Wc) _ _ (fun _ => False) HFr _ a Ha (fun x => x)).
      intros bw wlo whi x Hinw Hr. vm_compute in Hinw. destruct Hinw. }
  set (mdw := with_vm_backing _ _ _) in *.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ LP_KEPT0 HS (lp_env_agree regs1 0 0)
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (21%bv : bv 5) Q21. prreg HS (11%bv : bv 5) Q11.
  rewrite (lp_ew_reg _ _ _ 12 12%bv eq_refl) in Q21. rewrite (lp_ew_reg _ _ _ 26 26%bv eq_refl) in Q11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?j)) _ _) _) _ =>
    change (Z_to_bv 64 (BASE + j)) with (Z_to_bv 64 (BASE + LP_HEAD)) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
    assert (RA' : mf_regs_at B v lyc pos rg) by
      (apply (mf_regs_at_of B v lyc pos regs1 _ RA); apply HK; cbv [LP_KEPT0 In]; tauto) end.
  apply (LOOP0 v lyc Sc Wc _ memc mdc pos mcc cur line p rest _ _ CX LS FRM CORE CELLS RA' Hn Hne LP Hlong MOD).
  + lia.
  + intros j Hj. lia.
  + rewrite HK by (cbv [LP_KEPT0 In]; tauto). rewrite Z.add_0_r. exact R26.
  + rewrite Q11, Z.add_0_r. exact R26.
  + rewrite HK by (cbv [LP_KEPT0 In]; tauto). exact R10.
  + rewrite Q21. exact R12.
  + rewrite HK by (cbv [LP_KEPT0 In]; tauto). exact R16.
  + rewrite HK by (cbv [LP_KEPT0 In]; tauto). exact R27.
  + rewrite HK by (cbv [LP_KEPT0 In]; tauto). exact R20.
  + split; [exact HJ|]. split.
    * intros a Ha _. exact (K0 a Ha).
    * apply (mf_val_keep Wc Wc memc _ (fun _ => False) _ 8 _ (fun a Ha _ => K0 a Ha));
        [lia | change (Z.of_nat 8) with 8; lia | intros k0 _ [] | exact C136].
Qed.
End e.
End f.
End d.
