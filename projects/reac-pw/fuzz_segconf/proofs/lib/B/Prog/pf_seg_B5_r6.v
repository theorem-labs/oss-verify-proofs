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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 238 of its 280 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   the piece R6 -> HEAD (pred n) / DONE of lib/B/Prog/pf_seg_B5_d.v (the B5 segment lane of the image-B G3 walk owner, piece prover:
   a sub-lane, 2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk; the function's rule-24 record
   is the rule-24 lookup record).
   ADAPTED from the image-A G3 walk owner's image-A piece lib/A/Prog/pf_a5_tl.v a5_r6_ok (commit d2e34cbbaa80)
   and the unit owner's plain lib/Prog/pf_p2.v tail_holds (04f2be60e018), re-derived on image B's code: B's next-line
   pointer is s9 (A: s5) and the shadow base s4 = x20 (A: s6), the latch copies s6 -> s8 and s9 -> s11 (A: s5 -> s9).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 9 instructions + the slow path's 2 (0x88f5c
   `j` to the error stub excluded), no UBSan trap:
     R6 0x8860c srli a0,s9,0x3       check B#15 (load1 at s9 = p' = t + o): the shadow byte of p'
        0x88610 add a0,a0,s4
        0x88614 lb a0,0(a0)
        0x88618 bnez a0,0x88f54      slow path 0x88f54 andi a1,s9,7; 0x88f58 blt a1,a0,0x8861c (0x88f5c j 0x8924c,
                                     the error stub, never reached: the byte is addressable, pf_obj's sa_addr t
                                     (length s + 1))
        0x8861c lbu a0,0(s9)         the byte at p': s[o] (<> 0, the text has no NUL) when o < length s, the NUL
                                     when o = length s
        0x88620 mv s8,s6             lineno for the next line (INV_HEAD's s8)
        0x88624 mv s11,s9            p = p' (INV_HEAD's s11)
        0x88628 bnez a0,0x881f8      a byte left: HEAD at o, rest shorter than n (H_HEAD (pred n))
        0x8862c j 0x89114            the text's end: DONE; lines (skipn o s) = [] (pfA_facts.lines_skipn_end),
                                     so r_lines is the identity and H_DONE's post is b5_post's.
   The proof: a fresh seed whose one region is the text's byte at s9 (extra atom 32, trim_tr.v tt_entry's form),
   s4 the shadow base (the token executor's Bx, fact SB), a run of the token executor (the inline check's obligation
   is the byte's addressability), the branch on the byte, INV_HEAD / INV_DONE from pf_base kept (no byte written).
   No Section hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
  PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B5_d pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small facts (pf_a5_tl.v's) ---------- *)
Lemma b5r6_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b5r6_br_ne0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> negb (v =? 0) = b.
Proof. intros E n v b H Hv Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc. Qed.
Lemma b5r6_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* the slots INV_DONE names are four of PF_SL's *)
Lemma b5r6_sl_sub : forall rd b L L', (forall x, In x L' -> In x L) -> pf_sl rd b L -> pf_sl rd b L'.
Proof. intros rd b L L' Hs H. unfold pf_sl in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hs x Hx)). Qed.

Ltac b5r6_in := unfold PF_RL, b5_FI; cbn [In app]; repeat first [left; reflexivity | right].
Ltac b5r6_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* a register the run left as an atom of the seed: its value is the seed register's, from the cut's list R *)
Ltac b5r6_atom HS EE R :=
  lazymatch type of R with pf_rg ?rx _ =>
    b5r6_rreg HS; rewrite b5_den_atom0;
    lazymatch goal with |- ew _ ?nn = _ =>
      let k := eval vm_compute in (Z.of_nat nn) in
      transitivity (getr rx (Z_to_bv 5 k)); [apply EE; reflexivity | apply (b5_rg _ _ k _ R); b5r6_in] end end.
Ltac b5r6_atoms := repeat (apply Forall_cons; [split; [cbn [fst]; lia | cbn [fst]; vm_compute; reflexivity] |]); apply Forall_nil.

(* the seed at R6 (0x8860c): every register its own atom; atom 32 is the text's byte at s9 = t + o, the one region
   (read only, trim_tr.v tt_ss's form); s9 an application address, s4 the shadow base (the token executor's Bx) *)
Definition b5r6_regions : smem := [ YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition b5r6_facts : facts :=
  mkFacts [ (20%nat, mkAF SB SB 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition b5r6_ss : sstate := mkSS B5_R6 sr_atoms b5r6_regions None b5r6_facts.
Definition b5r6_Bx : sv := SOff 20 0.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the registers a run left as their own atoms keep the values they had *)
Lemma b5r6_rg_keep_pi : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hs, b5_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

(* the R6 seed (trim_tr.v tt_entry's form) *)
Definition b5r6_E (regs : bvmap 5 word) (C : Z) : env := Eimg (Ereg regs [Z_to_bv 64 C]).
Lemma b5r6_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc p C,
  getr regs 25 = w64 p -> getr regs 20 = w64 SB ->
  4096 <= p <= 2 ^ 47 - 1 -> 0 <= C <= 255 ->
  rdW W memc p = Some C ->
  st_ok_pi SEGS VAL (b5r6_E regs C) b5r6_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + B5_R6)) memc (seg_rom SEGS))).
Proof.
intros W regs memc p C H25 H20 Hp HC Hrd.
set (E := b5r6_E regs C).
assert (E25 : ew E 25 = Z_to_bv 64 p) by (subst E; unfold b5r6_E; rewrite (ew_Eimg_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E20 : ew E 20 = Z_to_bv 64 SB) by (subst E; unfold b5r6_E; rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 C) by (subst E; unfold b5r6_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold b5r6_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b5r6_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E25, unsigned_lit_small by lia.
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
  cbn [b5r6_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E20, E25, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* after a token run that writes nothing: the environment agrees with E0 below 33 (HAE), the memory is memc
   (KM), every byte present in memc is present (KP) (trim_tr.v tt_after) *)
Ltac b5r6_after E0 HAE KM KP :=
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
Ltac b5r6_awr := lazymatch goal with |- awr_ok ?sg ?Bx ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bx Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* pf_base and pf_st at a state the run reached without writing a byte: the same layout and frame state, the
   journal at the new state, every byte kept, the frame registers kept *)
Lemma b5r6_still : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (b5_FI B v) ->
  pf_st v pos (rdW Wc memc) cf cur nm k ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc /\ pf_st v pos (rdW Wc memc') cf cur nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc cf cur nm k HB HJ' KM HRG HST.
pose proof HB as (HCX & HFI & _ & _ & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & _ & HAR).
pose proof (b5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & HHC).
assert (K : b5_kept v pos (rdW Wc memc) (rdW Wc memc')).
{ split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
split.
- apply (b5_move B v pos lyc Sc Wc rX memc mdc sc Sc rX' memc' mdc' sc HB HJ').
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact K.
  + exact HRG.
  + destruct (b5_SHv v pos HG) as (_ & SH1 & SH2 & _).
    intros i Hi. rewrite (KM (pf_SH v pos + i)) by lia. exact (HFSH i Hi).
- exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm k HG HAR Hin EF K HHC HST).
Qed.

(* ======================= R6 (0x8860c): check B#15, the byte at p', HEAD or DONE ======================= *)
Lemma b5_r6_ok : forall n, H_HEAD B (pred n) -> H_DONE B -> H_R6 B n.
Proof.
intros n HH HD v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLC & HLT & HST & HRG).
pose proof HB as (HCX & HFI & _ & _ & _).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
pose proof (b5_text B _ _ _ _ _ _ _ _ _ HB) as (NZ & _ & HSTR & HADDR & HHT & HHC).
pose proof HLC as (Hole & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
(* the text lies in a live block: 4096 <= t, t + |s| + 1 <= alloc_ceiling *)
destruct HHT as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
pose proof (req_size_pos mt (proj1 Hm)) as [_ Hreq].
unfold pf_len in Hbt2.
(* the byte at p' = t + o: s's byte o, or its NUL when o = |s| *)
destruct HSTR as ((HZS & _) & _).
set (C := nth o (p_s v ++ [0]) 0).
assert (VC : rdW Wc memc (p_t v + Z.of_nat o) = Some C).
{ exact (HZS o ltac:(rewrite length_app; cbn [length]; lia)). }
destruct (aview_byte SEGS (w_H Wc) memc _ _ VC) as (_ & _ & _ & HCr).
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (p_t v) (pf_len v))
  by (destruct HADDR as (_ & _ & _ & HRA & _); exact HRA).
(* the seed *)
assert (R25 : getr rX (Z_to_bv 5 25) = w64 (p_t v + Z.of_nat o)) by (apply (b5_rg _ _ 25 _ HRG); b5r6_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SB) by (rewrite SB_SHADOW_OFF; apply (b5_rg _ _ 20 _ HRG0); b5r6_in).
pose proof (b5r6_entry Wc rX memc (p_t v + Z.of_nat o) C (b5r6_bvr rX 25%bv 25 _ eq_refl R25)
  (b5r6_bvr rX 20%bv 20 _ eq_refl R20) ltac:(lia) ltac:(lia) VC) as HS.
assert (HEI : img_env VAL A_LIM (b5r6_E rX C)) by (unfold b5r6_E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (b5r6_E rX C) k = getr rX r)
  by (intros k r Hk; unfold b5r6_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E25 : ew (b5r6_E rX C) 25 = Z_to_bv 64 (p_t v + Z.of_nat o)) by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl); exact R25).
assert (E20 : ew (b5r6_E rX C) 20 = Z_to_bv 64 SB) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (b5r6_E rX C) 32 = Z_to_bv 64 C)
  by (unfold b5r6_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI EE E25 E20 E32. generalize (b5r6_E rX C) as E0. intros E0 HS HEI EE E25 E20 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
assert (SHOK : sh_ok SEGS b5r6_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B5_R6)) with (Z_to_bv 64 (BASE + B5_R6)).
(* 0x8860c .. 0x88628: check B#15, the byte, s8 = s6, s11 = s9, up to `bnez a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold b5r6_Bx. rewrite (U_atom _ 20 SB E20), (U_atom _ 25 _ E25) by (unfold SB; lia). rewrite SB_SHADOW_OFF.
  exact (range_addressable_sub _ _ (p_t v) (pf_len v) (p_t v + Z.of_nat o) 1 HRA ltac:(lia) ltac:(unfold pf_len; lia)). }
{ b5r6_awr. }
b5r6_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a byte left: the next line, HEAD (pred n) *)
  pose proof (b5r6_br_ne0 _ 32 C _ (b5r6_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as CNZ.
  apply Bool.negb_true_iff, Z.eqb_neq in CNZ. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_HEAD. { b5r6_awr. }
  b5r6_after E0 HAE KM KP.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) => rename msn into msR end.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (EEn : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew En k = getr rX r)
      by (intros k r Hk; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite (proj1 HAE k) by lia; exact (EE k r Hk)) end.
  assert (Hos : (o < length (p_s v))%nat).
  { destruct (Nat.lt_ge_cases o (length (p_s v))) as [Hlt | Hge]; [exact Hlt|]. exfalso. apply CNZ.
    unfold C. rewrite app_nth2 by lia. replace (o - length (p_s v))%nat with 0%nat by lia. reflexivity. }
  assert (QFI : pf_rg (ms_regs msR) (b5_FI B v)).
  { apply (b5r6_rg_keep_pi _ _ msR (w_H Wc) rX _ HS EEn); [unfold b5_FI; b5r6_atoms | exact HRG0]. }
  assert (QL : pf_rg (ms_regs msR) (PF_RL v pos ++ [(27, p_t v + Z.of_nat o); (24, ln)])).
  { unfold pf_rg, PF_RL. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      b5r6_atom HS EEn HRG. }
  destruct (b5r6_still v pos lyc Sc Wc rX memc mdc (ms_regs msR) (ms_mem msR) _ PF_SC_HEAD cf cur nm _ HB HJ KM QFI HST)
    as (HB2 & HST2).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    refine (HH v pos lyc Sc Wc rg mm mdn cf cur nm o ln d _) end.
  split; [exact HB2|]. split; [exact HLC|]. split; [exact Hos|]. split; [lia|]. split; [exact HST2 | exact QL].
- (* the text's NUL: no line left, DONE *)
  pose proof (b5r6_br_ne0 _ 32 C _ (b5r6_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as CZ.
  apply Bool.negb_false_iff, Z.eqb_eq in CZ. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_DONE. { b5r6_awr. }
  b5r6_after E0 HAE KM KP.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) => rename msn into msR end.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (EEn : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew En k = getr rX r)
      by (intros k r Hk; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite (proj1 HAE k) by lia; exact (EE k r Hk)) end.
  assert (Hoe : o = length (p_s v)).
  { destruct (Nat.lt_ge_cases o (length (p_s v))) as [Hlt | Hge]; [|lia]. exfalso. apply NZ.
    assert (Hn0 : nth o (p_s v) 0 = 0) by (rewrite <- (app_nth1 (p_s v) [0] 0 Hlt); exact CZ).
    rewrite <- Hn0. apply nth_In. exact Hlt. }
  assert (QFI : pf_rg (ms_regs msR) (b5_FI B v)).
  { apply (b5r6_rg_keep_pi _ _ msR (w_H Wc) rX _ HS EEn); [unfold b5_FI; b5r6_atoms | exact HRG0]. }
  assert (Q21 : pf_rg (ms_regs msR) [(21, pf_SH v pos)]).
  { unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. b5r6_atom HS EEn HRG. }
  destruct (b5r6_still v pos lyc Sc Wc rX memc mdc (ms_regs msR) (ms_mem msR) _ PF_SC_HEAD cf cur nm _ HB HJ KM QFI HST)
    as (HB2 & HST2).
  pose proof HB2 as (HCX2 & HFI2 & HOBJ2 & HSL2 & HFSH2).
  pose proof HST2 as (HRC2 & _).
  unfold b5_post. rewrite (lines_skipn_end (p_s v) o ltac:(lia)).
  change (r_lines (cf, cur, nm) ln []) with (cf, cur, nm). cbn [fst].
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdn) _ =>
    refine (HD v pos lyc Sc Wc rg mm mdn cf _) end.
  split; [exact HCX2|]. split; [exact HFI2|]. split; [exact HOBJ2|]. split; [exact HRC2|].
  split; [|split; [exact HFSH2 | exact Q21]].
  apply (b5r6_sl_sub _ _ (PF_SL v pos)); [|exact HSL2].
  intros x Hx. cbn [In] in Hx. unfold PF_SL. cbn [In].
  repeat (destruct Hx as [<- | Hx]; [repeat first [left; reflexivity | right] |]). destruct Hx.
Qed.
End e.
End f.
End d.
