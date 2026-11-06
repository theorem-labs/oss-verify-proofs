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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 279 of its 324 lines of code are new or changed and 408 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece R5 -> TAIL / HDR / KEY (a B5 sub-lane of the image-B G3 walk owner, 2026-10-30):
   b5_r5_ok : H_TAIL B n -> H_HDR B n -> H_KEY B n -> H_R5 B n.
   ADAPTED from the image-A G3 walk owner's image-A segment lane on a working branch (lib/A/Prog/pf_a5_tl.v a5_r6_ok: a token
   run through an inline check, the branch on the byte, the exits; the R5 point of pf_a5_d.v) and the unit owner's UBSan
   piece walks (lib/U/Prog/pf_p2.v, the same C-level dispatch), re-derived on image B's code; the cut rebuild is
   the B5 segment lane's lib/B/Prog/pf_seg_B5_r2.v (b5r2_base_same), on B5's kit lib/B/Prog/pf_seg_B5_k.v.
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), reached from C when trim returned a0 = lp:
     0x88390 `mv s7,a0`                   s7 = lp (the trimmed line pf_tline s o, inside buf)
     0x88394 .. 0x883a0                  check B#7 (load1 at a0 = lp: `srli a0,a0,3; add a0,a0,s4; lb a0,0(a0);
                                         bnez a0,0x88f60`, slow path 0x88f60 `andi a1,s7,7; blt a1,a0,0x883a4`,
                                         error stub 0x89254 `mv a0,s7; jal errpath_load1`): the token executor's
                                         obligation is range_addressable of [lp, lp + 1), from the kit's
                                         b5_addr_buf (buf's shadow cells are 0 while buf is in scope), so the slow
                                         path returns or is not taken and the stub is never reached
     0x883a4 `lbu a0,0(s7)`               a0 = hd0 (pf_tline s o) (the seed's byte, atom 32)
     0x883a8 `beqz a0,0x88600`            empty line: TAIL at the next line (r_line = (cf, cur, nm), r_line_short)
     0x883ac `li a1,91`
     0x883b0 `bne a0,a1,0x883f8`          not '[': KEY (r_line = r_key); '[': falls to HDR 0x883b4 (r_header)
   9 of B5's 116 instructions walked (0x88390 .. 0x883b0, check B#7's four included; its slow path 0x88f60 ..
   0x88f68 and the stub 0x89254 .. 0x89258 are closed by the token executor's check discharge, not stepped), check
   B#7 discharged, no UBSan trap in the range, no call, no write. Section hypotheses: none. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
  PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B5_d pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_a5_tl.v's tl_ helpers, pf_seg_B5_r2.v's b5r2_ helpers) ---------- *)
Lemma b5r5_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v ->
  ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
Lemma b5r5_hd0_nth : forall l, nth 0 (l ++ [0]) 0 = hd0 l.
Proof. intros [|x l]; reflexivity. Qed.
(* a C string read through a reader that agrees with another at every address *)
Lemma b5r5_str_eq : forall (rd rd' : reader) p s, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  0 <= p -> p + Z.of_nat (length s) + 8 <= 2 ^ 64 -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s K H0 H1 ((HZ & HN) & HT).
split; [split; [|exact HN]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite K by lia. exact (HZ i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). rewrite K by lia. exact (HT x Hx).
Qed.
Ltac b5r5_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.

(* the seed at R5 (pf_a5_tl.v r6_ss's form): every register its own atom; atom 32 is the byte at a0 = lp, the one
   region (read only); a0 an application address, s4 (x20) the shadow base (the token executor's Bx) *)
Definition b5r5_regions : smem := [ YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition b5r5_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition b5r5_ss : sstate := mkSS B5_R5 sr_atoms b5r5_regions None b5r5_facts.
Definition b5r5_Bx : sv := SOff 20 0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition b5r5_E (regs : bvmap 5 word) (C : Z) : env := Eimg (Ereg regs [Z_to_bv 64 C]).
Lemma b5r5_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc p C,
  getr regs (Z_to_bv 5 10) = w64 p -> getr regs (Z_to_bv 5 20) = w64 SB ->
  4096 <= p <= 2 ^ 47 - 1 -> 0 <= C <= 255 ->
  rdW W memc p = Some C ->
  st_ok_pi SEGS VAL (b5r5_E regs C) b5r5_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + B5_R5)) memc (seg_rom SEGS))).
Proof.
intros W regs memc p C H10 H20 Hp HC Hrd.
set (E := b5r5_E regs C).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (subst E; unfold b5r5_E; rewrite (ew_Eimg_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 SB)
  by (subst E; unfold b5r5_E; rewrite (ew_Eimg_Ereg_nat regs _ 20 (Z_to_bv 5 20) eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 C)
  by (subst E; unfold b5r5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold b5r5_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b5r5_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H W) memc p C Hrd) as (b & Hb & Hv & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r, (unsigned_lit_small C), (unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst C. apply Z_to_bv_bv_unsigned.
  + rewrite ?Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [b5r5_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E20, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* after a token run that writes nothing: the environment agrees with E0 below 33 (HAE), the memory is memc (KM),
   every byte present in memc is present (KP) (pf_a5_tl.v tl_after) *)
Ltac b5r5_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree 33 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, apresent (w_H _) _ a -> apresent (w_H _) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.
Ltac b5r5_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* pf_base and pf_st at the same frame state after a run that kept every byte (pf_seg_B5_r2.v b5r2_base_same,
   with the spine state carried by the kit's b5_keep_st) *)
Lemma b5r5_still : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (b5_FI B v) ->
  pf_st v pos (rdW Wc memc) cf cur nm k ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc /\ pf_st v pos (rdW Wc memc') cf cur nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' cf cur nm k HB HJ' KM HRG HST.
pose proof HB as (HCX & HFI & _ & _ & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & _ & HAR).
pose proof HFI as (_ & _ & (f0 & HS0) & _).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc sc HB) as (_ & _ & _ & _ & _ & HCH).
assert (K : b5_kept v pos (rdW Wc memc) (rdW Wc memc')).
{ split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
split.
- apply (b5_move B v pos lyc Sc Wc rX memc mdc sc Sc rX' memc' mdc' sc HB HJ').
  + exists f0. rewrite HS0. rewrite b5_set_fs2. reflexivity.
  + apply Permutation_refl.
  + exact K.
  + exact HRG.
  + destruct (b5_SHv v pos HG) as (_ & SH1 & SH2 & _).
    intros i Hi. rewrite (KM (pf_SH v pos + i)) by lia. exact (HFSH i Hi).
- exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm k HG HAR Hin EF K HCH HST).
Qed.

(* ======================= R5 (0x88390): check B#7, the byte at lp, TAIL / KEY / HDR ======================= *)
Lemma b5_r5_ok : forall n, H_TAIL B n -> H_HDR B n -> H_KEY B n -> H_R5 B n.
Proof.
intros n HT HH HK v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HI.
pose proof HI as (HB & HLN & HL512 & HSTR & HINB & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (NUL & LS & HTSTR & HTADDR & HTH & HCH).
pose proof HLN as (HCTX & Ho & Hk & HST).
pose proof HGEO as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
unfold b5_len in HL512.
pose proof HINB as [HI1 HI2]. unfold b5_buf, PF_O_BUF in HI1, HI2.
pose proof (pf_tline_len_le (p_s v) o) as HTL.
(* the byte at lp: the trimmed line's first byte, or its NUL *)
assert (VC : rdW Wc memc lp = Some (hd0 (pf_tline (p_s v) o))).
{ destruct HSTR as ((HZ & _) & _). pose proof (HZ 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as E0.
  change (Z.of_nat 0) with 0 in E0. rewrite Z.add_0_r, b5r5_hd0_nth in E0. exact E0. }
pose proof (sa_aview_rng _ _ _ _ _ VC) as HCr.
(* check B#7's obligation: lp is an addressable byte of buf *)
pose proof (b5_addr_buf B v pos lyc Sc Wc rX memc mdc lp 1 HB ltac:(unfold b5_buf, PF_O_BUF; lia) ltac:(lia)
  ltac:(unfold b5_buf, PF_O_BUF; lia)) as HAB.
pose proof HAB as (_ & _ & _ & HRA & _).
(* the registers at R5 *)
rewrite !b5_rg_app in HRG. destruct HRG as (HRL & HRM & HR10).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 lp) by (apply (b5_rg rX _ 10 _ HR10); b5_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SB) by (rewrite SB_SHADOW_OFF; apply (b5_rg rX _ 20 _ HRG0); b5_in).
(* the seed *)
pose proof (b5r5_entry Wc rX memc lp (hd0 (pf_tline (p_s v) o)) R10 R20 ltac:(lia) ltac:(lia) VC) as HS.
assert (HEI : img_env VAL A_LIM (b5r5_E rX (hd0 (pf_tline (p_s v) o)))) by (unfold b5r5_E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (b5r5_E rX (hd0 (pf_tline (p_s v) o))) k = getr rX r)
  by (intros k r Hkr; unfold b5r5_E; apply ew_Eimg_Ereg_nat; exact Hkr).
assert (E10 : ew (b5r5_E rX (hd0 (pf_tline (p_s v) o))) 10 = Z_to_bv 64 lp)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E20 : ew (b5r5_E rX (hd0 (pf_tline (p_s v) o))) 20 = Z_to_bv 64 SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (b5r5_E rX (hd0 (pf_tline (p_s v) o))) 32 = Z_to_bv 64 (hd0 (pf_tline (p_s v) o)))
  by (unfold b5r5_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI EE E10 E20 E32. generalize (b5r5_E rX (hd0 (pf_tline (p_s v) o))) as E0.
intros E0 HS HEI EE E10 E20 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
assert (SHOK : sh_ok SEGS b5r5_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
(* every exit: the registers the run left as atoms, pf_base / pf_st at the run's state *)
assert (EXIT : forall En ss msR mdR, env_agree 33 E0 En -> st_ok_pi SEGS VAL En ss (restrict (w_H Wc) msR) ->
    ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
      (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc (ms_mem msR) mdR 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msR) a = rdW Wc memc a) ->
    (forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] -> sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0) ->
    pf_base B v pos lyc Sc Wc (ms_regs msR) (ms_mem msR) mdR PF_SC_LINE /\
    pf_st v pos (rdW Wc (ms_mem msR)) cf cur nm (length (skipn o (p_s v))) /\
    pf_rg (ms_regs msR) (PF_RL v pos ++ PF_RM v o ln)).
{ intros En ss msR mdR HAEn HSn HJn KMn HSR.
  assert (EEn : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew En k = getr rX r).
  { intros k r Hkr. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite (proj1 HAEn k) by lia. exact (EE k r Hkr). }
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
      getr (ms_regs msR) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H Wc) En ss msR (Z_to_bv 5 r) HSn), (HSR r Hr), b5_den_atom0.
    apply EEn. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
  assert (QFI : pf_rg (ms_regs msR) (b5_FI B v)).
  { unfold pf_rg, b5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b5_rg rX _ _ _ HRG0); b5_in | b5_in]). }
  destruct (b5r5_still v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs msR) (ms_mem msR) mdR cf cur nm _ HB HJn KMn
    QFI HST) as (HB2 & HST2).
  split; [exact HB2|]. split; [exact HST2|].
  unfold pf_rg. rewrite Forall_app. split.
  - unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b5_rg rX _ _ _ HRL); b5_in | b5_in]).
  - unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b5_rg rX _ _ _ HRM); unfold PF_RM; b5_in | b5_in]). }
unfold cfg_at. change (w64 (BASE + B5_R5)) with (Z_to_bv 64 (BASE + B5_R5)).
(* 0x88390 .. 0x883a8: s7 = lp, check B#7, the byte, up to `beqz a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold b5r5_Bx. rewrite (U_atom _ 20 SB E20), (U_atom _ 10 _ E10) by (unfold SB; lia).
  rewrite SB_SHADOW_OFF. exact (range_addressable_sub _ _ lp 1 lp 1 HRA ltac:(lia) ltac:(lia)). }
{ b5r5_awr. }
b5r5_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the empty line: TAIL at the next line *)
  rewrite ?branch_eq_U, ?branch_ne_U in Hc.
  rewrite (U_atom _ 32 _ (b5r5_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32)) in Hc by lia. rewrite ?U_lit in Hc by lia.
  assert (CZ : hd0 (pf_tline (p_s v) o) = 0) by (apply Z.eqb_eq; exact Hc). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_TAIL. { b5r5_awr. }
  b5r5_after E0 HAE KM KP.
  lazymatch type of HS with st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) =>
    destruct (EXIT En ssn msn _ HAE HS HJ KM ltac:(intros r Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr)) as (HB2 & HST2 & QL) end.
  rewrite (b5_post_step B v cf cur nm o ln Ho).
  replace (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) with (cf, cur, nm)
    by (rewrite (r_line_short cf cur nm (ln + 1) (p_s v) o HL512), CZ; reflexivity).
  unfold pf_postm.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx) end.
  apply (HT v pos lyc Sc Wc _ _ _ cf cur nm (pf_next (p_s v) o) (ln + 1) (d ++ [pf_line (p_s v) o])).
  pose proof (pf_next_skipn_lt (p_s v) o Ho) as HNL.
  destruct HST2 as (S1 & S2 & S3 & S4 & S5).
  split; [exact HB2|]. split; [exact (pf_lctx_next _ _ _ _ NUL HCTX Ho)|]. split; [lia|].
  split; [split; [exact S1|]; split; [exact S2|]; split; [exact S3|]; split; [eapply pf_cnt_mono; [|exact S4]; lia | exact S5]|].
  exact QL.
- (* a byte: '[' or not *)
  rewrite ?branch_eq_U, ?branch_ne_U in Hc.
  rewrite (U_atom _ 32 _ (b5r5_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32)) in Hc by lia. rewrite ?U_lit in Hc by lia.
  assert (CNZ : hd0 (pf_tline (p_s v) o) <> 0) by (apply Z.eqb_neq; exact Hc). clear Hc.
  (* 0x883ac `li a1,91`, up to `bne a0,a1` *)
  paj_run_tok RUN HS HJ SHOK Bspan. { b5r5_awr. }
  b5r5_after E0 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* not '[': KEY *)
    rewrite ?branch_eq_U, ?branch_ne_U in Hc.
    rewrite (U_atom _ 32 _ (b5r5_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32)) in Hc by lia. rewrite ?U_lit in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc. rename Hc into CNB.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_KEY. { b5r5_awr. }
    b5r5_after E0 HAE KM KP.
    lazymatch type of HS with st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) =>
      assert (Q23 : getr (ms_regs msn) (Z_to_bv 5 23) = w64 lp)
        by (b5r5_rreg HS; rewrite b5_den_atom0; rewrite (proj1 HAE 10%nat) by lia; exact E10);
      destruct (EXIT En ssn msn _ HAE HS HJ KM ltac:(intros r Hr; cbn [In] in Hr;
        repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr)) as (HB2 & HST2 & QL) end.
    rewrite (b5_post_step B v cf cur nm o ln Ho).
    replace (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) with (r_key cf cur nm (ln + 1) (pf_tline (p_s v) o))
      by (rewrite (r_line_short cf cur nm (ln + 1) (p_s v) o HL512);
          destruct (Z.eqb_spec (hd0 (pf_tline (p_s v) o)) 0) as [E|_]; [exfalso; exact (CNZ E)|];
          destruct (Z.eqb_spec (hd0 (pf_tline (p_s v) o)) 91) as [E|_]; [exfalso; exact (CNB E) | reflexivity]).
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_KEY) rg mm mdx) end.
    apply (HK v pos lyc Sc Wc _ _ _ cf cur nm o ln (d ++ [pf_line (p_s v) o]) lp).
    split; [exact HB2|]. split; [eapply b5_mid; [exact NUL | exact (conj HCTX (conj Ho (conj Hk HST2)))]|].
    split; [exact HST2|]. split; [exact HL512|].
    split; [apply (b5r5_str_eq (rdW Wc memc)); [exact KM | lia | lia | exact HSTR]|].
    split; [exact HINB|]. split; [exact CNZ|]. split; [exact CNB|].
    unfold pf_rg in QL |- *. rewrite app_assoc. apply Forall_app. split; [exact QL|].
    apply Forall_cons; [cbn [fst snd]; exact Q23 | apply Forall_nil].
  + (* '[': HDR *)
    rewrite ?branch_eq_U, ?branch_ne_U in Hc.
    rewrite (U_atom _ 32 _ (b5r5_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32)) in Hc by lia. rewrite ?U_lit in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc. rename Hc into CB.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_HDR. { b5r5_awr. }
    b5r5_after E0 HAE KM KP.
    lazymatch type of HS with st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) =>
      assert (Q23 : getr (ms_regs msn) (Z_to_bv 5 23) = w64 lp)
        by (b5r5_rreg HS; rewrite b5_den_atom0; rewrite (proj1 HAE 10%nat) by lia; exact E10);
      destruct (EXIT En ssn msn _ HAE HS HJ KM ltac:(intros r Hr; cbn [In] in Hr;
        repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr)) as (HB2 & HST2 & QL) end.
    rewrite (b5_post_step B v cf cur nm o ln Ho).
    replace (r_line cf cur nm (ln + 1) (pf_line (p_s v) o)) with (r_header cf nm (ln + 1) (pf_tline (p_s v) o))
      by (rewrite (r_line_short cf cur nm (ln + 1) (p_s v) o HL512);
          destruct (Z.eqb_spec (hd0 (pf_tline (p_s v) o)) 0) as [E|_]; [exfalso; exact (CNZ E)|];
          destruct (Z.eqb_spec (hd0 (pf_tline (p_s v) o)) 91) as [_|E]; [reflexivity | exfalso; exact (E CB)]).
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_HDR) rg mm mdx) end.
    apply (HH v pos lyc Sc Wc _ _ _ cf cur nm o ln (d ++ [pf_line (p_s v) o]) lp).
    split; [exact HB2|]. split; [eapply b5_mid; [exact NUL | exact (conj HCTX (conj Ho (conj Hk HST2)))]|].
    split; [exact HST2|]. split; [exact HL512|].
    split; [apply (b5r5_str_eq (rdW Wc memc)); [exact KM | lia | lia | exact HSTR]|].
    split; [exact HINB|]. split; [exact CB|].
    unfold pf_rg in QL |- *. rewrite app_assoc. apply Forall_app. split; [exact QL|].
    apply Forall_cons; [cbn [fst snd]; exact Q23 | apply Forall_nil].
Qed.
End e.
End f.
End d.
