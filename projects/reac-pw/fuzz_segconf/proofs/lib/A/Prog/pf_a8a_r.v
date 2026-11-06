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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 697 of its 751 lines of code are new or changed and 399 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A8a's bound branch of reac_segconf_parse_file's walk,
   the theorem a8_kf_main: from 0x887f0 (BASE + PF_A8F, no entry of c holds the header's name, lib/A/Prog/pf_a8a_k.v
   a8F) to NEW when n < 32, else check #30, c->overflow++, the refuse call at 0x88834 and the jump to CLR. Part of
   segment A8a's proof, by the G3 walk owner, 2026-10-30. Rule 24: proves function reac_segconf_parse_file (segment
   A8a; reuse search and CONFIRM in the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md;
   reuse verdict none: written new). The functional template is the plain-build walk owner's plain piece
   lib/Prog/pf_p4.v at 16c6d72c0344 (w_notfound), the refuse call that of lib/A/Prog/pf_a7_u.v at
   commit 89bf60b43b36.
   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s lines 864-882, 1102-1105):
     0x887f0 li a0,0x20 ; blt s3,a0,NEW                       n < 32: NEW 0x8890c (INV_NEW by a8_new_ok)
     0x887f8 ld a0,0x20(s1) ; srli/add/lb/bnez 0x88ba8        check #30 (load4 of c->overflow), stub 0x88ba8
     0x8880c lw a1,0(a0) ; addi a1,1 ; sw a1,0(a0)            c->overflow++ (seg_get, R:110)
     0x88818 auipc/addi a2 = 0x215c0 (F_bound, listing object 67) ; a4 = 32 ; s8 = c (slot 0x90) ; a0 = c ;
             a1 = s10 (ln + 1) ; a3 = s9 (np, the name in buf)
     0x88834 jal refuse ; 0x88838 j 0x880fc (CLR)
   The walk: a register-only seed at 0x887f0 runs `li` and decides `blt` (a8r_blt32); on n < 32 a run to NEW and
   HA_NEW; on n = 32 a run to 0x887f8, a second seed there (a8r_seedB: the slots s1 + 0x20 and s1 + 0x90, the field
   c->overflow writable, the block shadow entry that passes check #30 with the literal 0 shadow byte), one token run
   to the call, pf_base at the call state (a8r_base_store: only c->overflow's 4 bytes changed), c's new state
   a8_ovf cf (a8r_stored, a8r_rconf_store), the closed site lemma refuse_site_ok_88834 (VERIFY rule 1j-bis), the call
   through PaFx.cl_callSF with the frame chain of pf_a5_k.a5_chain, pf_base at the FP state refuse returned
   (pf_a6_k.a6_keeps_refuse, a6_base_move), INV_CLR there, and the one `j` to CLR (a8r_ret, any FP state).
   Section hypotheses: REF (refuse_contract at image A's numbers, every FP state), SIGP (the call target
   pa_sigma SS_refuse is BASE + AF_refuse), OBJ (the auipc / addi pair's object atom A_OBJ 67 is
   seg_litA_rc F_bound = 0x215c0), VRO and SSPX (used only at a6_base_move after the refuse call). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pfA_facts check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_k pf_a6_k pf_a8a_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** Pure facts *)
(* a byte of the low 4 bytes depends only on the value mod 2 ^ 32 *)
Lemma a8r_byte_low : forall V w i, 0 <= i < 4 -> V mod 2 ^ 32 = w mod 2 ^ 32 ->
  Z.shiftr V (8 * i) mod 256 = Z.shiftr w (8 * i) mod 256.
Proof.
intros V w i Hi H. change 256 with (2 ^ 8). apply Z.bits_inj'. intros m Hm.
destruct (Z.lt_ge_cases m 8) as [Hlt | Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite <- (Z.mod_pow2_bits_low V 32 (m + 8 * i)) by lia.
  rewrite <- (Z.mod_pow2_bits_low w 32 (m + 8 * i)) by lia. rewrite H. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
(* the value the store at 0x88814 takes: sext32(c->overflow) + 1, whose low 32 bits are overflow + 1 *)
Lemma a8r_mod64_32 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. apply Z.bits_inj'. intros m Hm. destruct (Z.lt_ge_cases m 32) as [Hlt | Hge].
- rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma a8r_inc_U : forall E k ovf, bv_unsigned (ew E k) = ovf -> 0 <= ovf < 2 ^ 32 ->
  U E (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1)) mod 2 ^ 32 = (ovf + 1) mod 2 ^ 32.
Proof.
intros E k ovf Hk Ho. rewrite U_SAlu, U_SExt, U_SOff, U_SLit, Hk, Z.add_0_r.
rewrite (zcanon_small ovf) by lia. cbn [zalu_raw].
change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small ovf (2 ^ 32)) by lia.
assert (SW : bv_swrap 32 ovf mod 2 ^ 32 = ovf mod 2 ^ 32).
{ unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). rewrite Zminus_mod_idemp_l. f_equal. ring. }
set (s := bv_swrap 32 ovf) in *. clearbody s.
unfold zcanon, M64.
rewrite a8r_mod64_32.
rewrite (Z.add_mod (s mod 2 ^ 64) (1 mod 2 ^ 64) (2 ^ 32)) by (compute; discriminate).
rewrite !a8r_mod64_32, SW.
rewrite <- Z.add_mod by (compute; discriminate). reflexivity.
Qed.
(* `blt s3, a0` with a0 = 32 and s3 = n *)
Lemma a8r_blt32 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 32)) = (v <? 32).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !a8_swrap_small by lia.
reflexivity.
Qed.
(* the counters' room at the next line, after c->overflow + 1 and one refusal *)
Lemma a8r_cnt : forall cf k k' l f a, (k' < k)%nat -> pf_cnt cf k -> pf_cnt (refuse (a8_ovf cf) l f a) k'.
Proof.
unfold pf_cnt. intros cf k k' l f a Hk [H1 H2]. rewrite PFA.pfa_refuse_refused.
destruct (refuse_proj (a8_ovf cf) l f a) as (_ & Ho & _). rewrite Ho. unfold a8_ovf. cbn [rc_refused rc_overflow].
split; lia.
Qed.
(* a C string whose read span is kept *)
Lemma a8r_str_keep : forall (rd rd' : reader) q s, sa_str rd q s ->
  (forall a, q <= a < q + seg_spec.cstr_span q s -> rd' a = rd a) -> sa_str rd' q s.
Proof.
intros rd rd' q s ((Hz & Hn) & Ht) K. split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite K; [exact (Hz i Hi)|]. unfold seg_spec.cstr_span.
  pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
- intros x Hx. rewrite K; [exact (Ht x Hx)|]. unfold seg_spec.cstr_span. Z.div_mod_to_equations. lia.
Qed.
(* c's new bytes: the old ones off c->overflow, overflow + 1 at it (a8_rconf_ovf) *)
Lemma a8r_rconf_store : forall (rd rd' : reader) c cf, sa_rconf rd c cf -> rc_overflow cf + 1 < 2 ^ 32 ->
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_OVERFLOW <= i < seg_spec.RC_OVERFLOW + 4) ->
     rd' (c + i) = rd (c + i)) ->
  sa_val rd' (c + seg_spec.RC_OVERFLOW) 4 (rc_overflow cf + 1) ->
  sa_rconf rd' c (a8_ovf cf).
Proof.
intros rd rd' c cf (bs & HB & Henc) Hov K V.
pose proof Henc as (Lbs & _ & _ & _ & _ & _ & _ & _ & ((OV0 & _) & _) & _).
unfold seg_spec.SEG_C_SIZE in Lbs.
set (ws := PMem.le4 (Z_to_bv 64 (rc_overflow cf + 1))).
assert (Lw : length ws = 4%nat) by apply PMem.length_le4.
exists (PMem.upd_bytes bs (Z.to_nat seg_spec.RC_OVERFLOW) ws).
split; [|exact (a8_rconf_ovf cf bs Henc Hov)].
unfold seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *.
intros i Hi. rewrite PMem.upd_bytes_length in Hi by lia.
assert (En : nth_error (PMem.upd_bytes bs (Z.to_nat 13520) ws) i =
  Some (nth i (PMem.upd_bytes bs (Z.to_nat 13520) ws) ZB0))
  by (apply nth_error_nth'; rewrite PMem.upd_bytes_length by lia; exact Hi).
rewrite a8_upd_nth_error in En by lia.
destruct (Nat.lt_ge_cases i (Z.to_nat 13520)) as [Hlo | Hge];
  [|destruct (Nat.lt_ge_cases i (Z.to_nat 13520 + 4)) as [Hin | Hhi]].
- replace ((Z.to_nat 13520 <=? i)%nat && (i <? Z.to_nat 13520 + length ws)%nat) with false in En
    by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
  rewrite (nth_error_nth' bs ZB0) in En by lia. injection En as En. rewrite <- En.
  rewrite K by lia. exact (HB i ltac:(lia)).
- replace ((Z.to_nat 13520 <=? i)%nat && (i <? Z.to_nat 13520 + length ws)%nat) with true in En
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]).
  rewrite (nth_error_nth' ws ZB0) in En by lia. injection En as En. rewrite <- En.
  replace (c + Z.of_nat i) with (c + 13520 + Z.of_nat (i - Z.to_nat 13520)) by lia.
  rewrite (V (i - Z.to_nat 13520)%nat) by lia. f_equal.
  subst ws. rewrite <- (a8_le4_byte (rc_overflow cf + 1) (i - Z.to_nat 13520)) by lia. reflexivity.
- replace ((Z.to_nat 13520 <=? i)%nat && (i <? Z.to_nat 13520 + length ws)%nat) with false in En
    by (symmetry; apply andb_false_iff; right; apply Nat.ltb_ge; lia).
  rewrite (nth_error_nth' bs ZB0) in En by lia. injection En as En. rewrite <- En.
  rewrite K by lia. exact (HB i ltac:(lia)).
Qed.

(** ** The symbolic states *)
(* 0x887f8: the slots s1 + 0x20 (&c->overflow) and s1 + 0x90 (c), the field c->overflow (atom 33) of the block c
   (atom 32), writable *)
Definition PF_A8S : Z := AF_reac_segconf_parse_file + 0xd80.    (* 0x887f8 *)
Definition a8r_slots : YP09.region := YP09.mkRegion (Some 9%nat) 0x20 0x98 0 0
  [YP09.mkChunk 0x20 (CVal 8 (SOff 32 seg_spec.RC_OVERFLOW)); YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))].
Definition a8r_creg : YP09.region := YP09.mkRegion (Some 32%nat) seg_spec.RC_OVERFLOW (seg_spec.RC_OVERFLOW + 4)
  seg_spec.RC_OVERFLOW (seg_spec.RC_OVERFLOW + 4) [YP09.mkChunk seg_spec.RC_OVERFLOW (CVal 4 (SOff 33 0))].
Definition a8r_F : facts := mkFacts [(2%nat, a8_spF); (9%nat, a8_spF); (22%nat, mkAF SB SB 0); (32%nat, PTR 4)] [] [].
Definition ss_a8r_B : sstate := mkSS PF_A8S sr_atoms [a8r_slots; a8r_creg] None a8r_F.
Definition a8r_SH : list shent := [mkSHE 32 0 seg_spec.SEG_C_SIZE].

(* the walk's tactics (pf_a8a_s.v's, copied: Ltacs of a section do not survive it) *)
Ltac a8_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac a8_kept_empty HFr K lo hi :=
  lazymatch goal with |- SRr ?segs _ _ _ =>
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview segs H m1) (aview segs H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := segs) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end end.
Ltac a8_regs_kept HS EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold A8_REGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
        let QX := fresh "QX" in prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX;
        rewrite ?ew_havoc_old by (cbn; lia); apply EE; reflexivity end |]);
  destruct Hr.
(* one register the run kept, read through the seed's environment *)
Ltac a8r_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
    let QX := fresh "QX" in prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX; apply EE; reflexivity end.

(** ** The return 0x88838 -> CLR, at any FP state *)
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f0.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e0.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* a register-only seed at a pc (sp's fact only; pf_a8a_s.v's a8_seed_regs) *)
Lemma a8r_seed_regs : forall pc rX (W : world SEGS) memc v,
  getr rX (Z_to_bv 5 2) = w64 (pf_s1 v) -> 2 ^ 46 <= pf_s1 v <= 2 ^ 47 -> pf_s1 v mod 32 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (mkSS pc sr_atoms [] None (mkFacts [(2%nat, a8_spF)] [] []))
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS a8_Bx [] (Eimg (Ereg rX [])) (mrestrict (w_H W) memc).
Proof.
intros pc rX W memc v R2 Hs Hal. split; [|apply Forall_nil].
assert (U2 : bv_unsigned (ew (Eimg (Ereg rX [])) 2) = pf_s1 v) by (apply (a8_u_reg rX _ 2); [lia | exact R2 | lia]).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, a8_spF. cbn [af_lo af_hi af_al2].
  rewrite U2. change (2 ^ 5) with 32. lia.
Qed.

(* 0x88838 `j 0x880fc`: refuse's return address is one jump before CLR; no register, no byte changes *)
Lemma a8r_ret : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d,
  H_CLR B n -> INV_CLR B n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + PF_A8RR)) memc (seg_rom SEGS)) mdc) (pf_postm B v (cf, None, nm) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d HCLR HI.
pose proof HI as (HB & HMID & HST & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (A1 & _).
rewrite SPF in G1.
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & (HJ & Hly & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by exact (a5_rg_get rX _ 2 _ HFI ltac:(cbn; tauto)).
destruct (a8r_seed_regs PF_A8RR rX Wc memc v R2 ltac:(lia) G5) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
remember (Eimg (Ereg rX [])) as E eqn:HE. clear HE.
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_CLR.
{ apply awr_ok_nil. }
a8_md.
lazymatch type of HF with frame_of _ _ ?m1 ?m2 => assert (Hmem : m2 = m1) end.
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). destruct Hr. }
clear HF HFr HG.
pmkst HS. rewrite Hmem in HJ |- *.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 24; 26; 27] -> getr rT (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
end.
{ intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [a8r_kept HS EE|]). destruct Hr. }
apply (HCLR v pos lyc Sc Wc _ memc _ cf nm o ln d).
split; [|split; [exact HMID | split; [exact HST|]]].
- split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  refine (conj HJ (conj Hly (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM _))))))).
  apply (a8_rg_keep rX); [exact HFI|]. intros rv Hrv. apply KR. try unfold a5_FI in Hrv. cbn [In] in Hrv.
  repeat (destruct Hrv as [<- | Hrv]; [cbn; tauto|]). destruct Hrv.
- apply (a8_rg_keep rX); [exact HRG|]. intros rv Hrv. apply KR. unfold PF_RM in Hrv. cbn [In app] in Hrv.
  repeat (destruct Hrv as [<- | Hrv]; [cbn; tauto|]). destruct Hrv.
Qed.

End e0.
End f0.
End d0.

(** ** The bound branch *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the seed environment at 0x887f8: atom 32 = c, atom 33 = c->overflow *)
Definition a8r_E (rX : bvmap 5 word) (c ovf : Z) : env := Eimg (Ereg rX [w64 c; w64 ovf]).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* refuse's contract at image A's numbers (pf_pieces.v's segment list for A8a), at every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v; the pinned instance gives each by
   computation): the call target pa_sigma SS_refuse, the object atom of 0x88818's auipc / addi pair, the read-only
   range *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A; discharged by SegRecCells.seg_rec_cells
   when listing stage 2 compiles) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a2 at the call: listing object 67 is .str.10, F_bound's text (SegInstA.v's map, 0x215c0) *)
Lemma a8r_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 67) = w64 (seg_litA_rc F_bound).
Proof using OBJ.
intros E HE. rewrite (img_env_atomP E (A_OBJ 67) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 67%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Lemma a8r_E_facts : forall (rT : bvmap 5 word) c ovf, 0 <= c < 2 ^ 64 -> 0 <= ovf < 2 ^ 64 ->
  img_env VAL A_LIM (a8r_E rT c ovf) /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (a8r_E rT c ovf) k = getr rT r) /\
  ew (a8r_E rT c ovf) 32 = w64 c /\ bv_unsigned (ew (a8r_E rT c ovf) 32) = c /\
  bv_unsigned (ew (a8r_E rT c ovf) 33) = ovf.
Proof.
intros rT c ovf Hc Ho.
assert (E32 : ew (a8r_E rT c ovf) 32 = w64 c)
  by (unfold a8r_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rT _ 0)).
assert (E33 : ew (a8r_E rT c ovf) 33 = w64 ovf)
  by (unfold a8r_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rT _ 1)).
split; [apply Eimg_env|]. split; [intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk|].
split; [exact E32|]. split; [rewrite E32; unfold w64; apply unsigned_lit_small; lia|].
rewrite E33; unfold w64; apply unsigned_lit_small; lia.
Qed.

(* the state at 0x887f8 satisfies ss_a8r_B, and the block's shadow entry holds *)
Lemma a8r_seedB : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  a8c B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  st_ok_pi SEGS VAL (a8r_E rX (p_c v) (rc_overflow cf)) ss_a8r_B
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_A8S)) memc (seg_rom SEGS))) /\
  sh_ok SEGS a8_Bx a8r_SH (a8r_E rX (p_c v) (rc_overflow cf)) (mrestrict (w_H Wc) memc).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (HB & HM & HST & HS & HI & HL & HR).
destruct HB as (HCX & HFI & HOB & HSL & HFSH).
destruct HFI as (HJ & Hly & HSc & HPm & HSV & HFL & HFRM & HRF).
destruct HOB as (OT & OTA & OTH & OCA & OCH & OCAT & OLIT & OROD & OSSP).
destruct HST as (SRC & SNM & SCNT).
pose proof (proj1 HJ) as HAR.
pose proof (a8_sp B v HCX) as (S1 & S2 & S3 & S4 & S5).
pose proof HCX as (_ & _ & _ & Hc64 & _ & _ & _ & _ & (fe & (RP & _)) & _).
pose proof RP as (C0 & C16 & _).
destruct OCH as (bc & mc & Hinc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hinc) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
destruct SRC as (bs & HBs & Henc). pose proof Henc as (Lbs & _ & _ & _ & _ & _ & _ & _ & OV & _).
pose proof OV as ((OV0 & OV1) & _).
unfold seg_spec.SEG_C_SIZE in Lbs, Hbc2.
assert (VO : sa_val (rdW Wc memc) (p_c v + seg_spec.RC_OVERFLOW) 4 (rc_overflow cf))
  by (apply (a8_u32_at _ (p_c v) bs seg_spec.RC_OVERFLOW (rc_overflow cf) HBs);
      [unfold seg_spec.RC_OVERFLOW; lia | unfold seg_spec.RC_OVERFLOW; lia | exact OV]).
destruct (a8r_E_facts rX (p_c v) (rc_overflow cf) ltac:(lia) ltac:(lia)) as (_ & _ & E32 & U32 & U33).
set (E := a8r_E rX (p_c v) (rc_overflow cf)) in *.
assert (U2 : bv_unsigned (ew E 2) = pf_s1 v)
  by (apply (a8_u_reg rX _ 2); [lia | exact (a5_rg_get rX _ 2 _ HRF ltac:(cbn; tauto)) | lia]).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (apply (a8_u_reg rX _ 9); [lia | exact (a5_rg_get rX _ 9 _ HRF ltac:(cbn; tauto)) | lia]).
assert (U22 : bv_unsigned (ew E 22) = SB)
  by (apply (a8_u_reg rX _ 22); [lia | exact (a5_rg_get rX _ 22 _ HRF ltac:(cbn; tauto)) | unfold SB; lia]).
split.
- rewrite restrict_mkst_fx. unfold ss_a8r_B. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, a8r_slots.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x20 8 _ (p_c v + seg_spec.RC_OVERFLOW));
           [apply (a8_soff E 32 _ _ U32) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.RC_OVERFLOW; lia
           | cbn; lia |].
         apply val_mem_of_rdword. apply (a8_sl_get _ _ (PF_SL v pos) _ _ HSL). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x90 8 _ (p_c v));
           [rewrite (a8_soff E 32 0 _ U32), Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
           | cbn; lia |].
         apply val_mem_of_rdword. apply (a8_sl_get _ _ (PF_SL v pos) _ _ HSL). unfold PF_SL. cbn [In]. tauto.
    * unfold region_ok, a8r_creg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [unfold seg_spec.RC_OVERFLOW; lia|]. split; [unfold seg_spec.RC_OVERFLOW; lia|].
      split.
      { intros o0 Ho0. apply (apresent_writable SEGS).
        exact (proj1 (Hppres (p_c v + o0) ltac:(unfold seg_spec.RC_OVERFLOW in Ho0; lia))). }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (p_c v) seg_spec.RC_OVERFLOW 4 (SOff 33 0) (rc_overflow cf));
        [rewrite (a8_soff E 33 0 _ U33), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      exact (a8_val_mem_of_sa SEGS _ _ _ _ _ VO).
  + apply pairwise_disjoint_of_extents. unfold a8r_slots, a8r_creg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold seg_spec.RC_OVERFLOW.
    repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok a8r_F]. unfold afact_ok, a8_spF, PTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U22, U32. change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat split; try lia.
- unfold sh_ok, a8r_SH. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart, a8_Bx. cbn [she_m she_lo she_hi].
  assert (UB : U E (SOff 22 0) = SB) by (rewrite U_SOff, U22, Z.add_0_r; apply zcanon_small; unfold SB; lia).
  assert (UC : U E (SOff 32 0) = p_c v) by (rewrite U_SOff, U32, Z.add_0_r; apply zcanon_small; lia).
  rewrite UB, UC. split.
  + rewrite Z.add_0_r, Z.sub_0_r. exact (proj1 (proj2 (proj2 (proj2 OCA)))).
  + intros y Hy. unfold seg_spec.SEG_C_SIZE in *. rewrite Z.min_l, Z.max_r in Hy by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.

(* the four bytes the store at 0x88814 leaves, read from the region's chunk after the run *)
Lemma a8r_stored : forall E k ovf (H : word -> bool) (m : word -> option byte) base off,
  bv_unsigned (ew E k) = ovf -> 0 <= ovf -> ovf + 1 < 2 ^ 32 ->
  YP09.chunk_ok SEGS E (mrestrict H m) base
    (YP09.mkChunk off (CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff k 0)) (SLit 1)))) ->
  sa_val (aview SEGS H m) (base + off) 4 (ovf + 1).
Proof.
intros E k ovf H m base off Hk H0 H1 Hck j Hj.
destruct (Hck (Z.of_nat j) ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold byte_of_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small (ovf + 1) (2 ^ 32)) by lia.
apply a8r_byte_low; [lia|].
exact (a8r_inc_U E k ovf Hk ltac:(lia)).
Qed.

(* pf_base at a state whose reader differs from the cut's only in [lo, hi), inside the block c: what the store
   c->overflow++ leaves (no Section hypothesis: the image bytes, the stack-protector cells and the read-only window
   are off the block, which is off the image) *)
Lemma a8r_base_store : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' lo hi,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  p_c v <= lo -> hi <= p_c v + seg_spec.SEG_C_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' lo hi (CX & FI & OBJ0 & SL & FSH) HJ' Hlo Hhi K HRG.
destruct (a6_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (a6_frame B v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (a6_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & HSf & HPerm & HSV & HFLW & HFRM & _).
destruct OBJ0 as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ') as HAR'. pose proof (proj1 HJ) as HAR.
pose proof alloc_ceiling_lt as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & Hc3 & Hc4 & Hcapp).
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
  as (bt & mt & Hint & Hbt1 & Hbt2 & Hbt3 & Hbt4 & _).
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hinc) as Hoff. unfold off_img in Hoff.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFE, E5 in Hsep.
(* every byte off the block c is kept *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (bc <= a < bc + req_size mc) -> rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha Hn. apply K; [exact Ha|]. intros Hw. apply Hn. unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (K3 : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
  rdW Wc memc' x = rdW Wc memc x).
{ intros x Hx _ _. pose proof (pa_img_range x Hx) as Hxr. unfold kImgEnd in Hxr.
  apply KB; [lia|]. unfold kImgEnd in *. lia. }
assert (KW : forall a, 65536 <= a -> a + 8 <= kImgEnd -> rdword (rdW Wc memc') a = rdword (rdW Wc memc) a).
{ intros a H1 H2. apply rdword_ext. intros k Hk. apply KB; unfold kImgEnd in *; lia. }
split; [exact CX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSf|]. split; [exact HPerm|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply KB; lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply KB; rewrite ?E5; lia. }
  split; [exact HFRM | exact HRG]. }
split.
{ split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      unfold sa_disj, seg_spec.cstr_span in HDJ.
      pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)).
      rewrite K; [exact (Hz i Hi) | lia | unfold seg_spec.SEG_C_SIZE in *; lia].
    - intros x Hx. apply (AR_block_word_vis SEGS B lyc Sc Wc memc' mdc' bt mt (p_t v + Z.of_nat (length (p_s v))) x HAR');
        [exact Hint | lia | lia]. }
  split; [exact (a6_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR' HT ltac:(unfold pf_len; lia))|].
  split; [exact HT|].
  split; [exact (a6_heap_addr B lyc Sc Wc memc' mdc' _ _ HAR' HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC|].
  split; [exact (a6_cat_move B _ Wc memc' CAT K3)|].
  split; [intros x Hx; exact (a6_lit_move B _ Wc memc' _ _ (LITS x Hx) K3)|].
  split.
  { intros a Hro Ho He.
    assert (Hlw : 65536 <= a < kImgEnd).
    { destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
      - apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
      - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia. }
    rewrite KB; [exact (ROD a Hro Ho He) | unfold kImgEnd in *; lia | unfold kImgEnd in *; lia]. }
  destruct SSP as (S1 & g & S2). split.
  - rewrite KW; [exact S1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia].
  - exists g. rewrite KW; [exact S2 | unfold guardA; lia | unfold guardA, kImgEnd; lia]. }
split.
{ apply (a6_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (a6_PF_SL_offs v pos)); [lia | lia |].
  intros a Ha. apply KB; lia. }
intros i Hi.
assert (ESH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
rewrite KB; [exact (FSH i Hi) | unfold SHADOW_OFF in *; lia |].
apply (a6_band_not_app bc (req_size mc) _ Hcapp). lia.
Qed.

(* VERIFY rule 1j-bis, edge reac_segconf_parse_file -> refuse at 0x88834 (refuse(c, lineno, F_bound, name, 32),
   R:110-111): at the jal, the state's pf_base, c holding a8_ovf cf (after c->overflow++), the counters' room of
   the cut, the name in buf and the call's registers give refuse_contract's premises besides afn_pre *)
Lemma refuse_site_ok_88834 : forall n v pos lyc Sc Wc rX memc mdc cf o ln d np name (regsc : bvmap 5 word),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> pf_mid v o ln d n ->
  sa_rconf (rdW Wc memc) (p_c v) (a8_ovf cf) -> pf_cnt cf (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) np name -> pf_inb (pf_F v pos + PF_O_BUF) np name ->
  getr regsc 2 = w64 (pf_s1 v) -> getr regsc 13 = w64 np -> getr regsc 14 = w64 32 ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc F_bound)
    [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17] (a8_ovf cf) (ln + 1) F_bound
    [AS name; AI 32] /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf o ln d np name regsc BASE0 MID RC CNT Hxs Hxb R2 R13 R14.
pose proof BASE0 as (CX & FI & OBJ0 & SL & FSH).
destruct (a6_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof FI as (HJ & Hly & _ & _ & _ & _ & HFRM & HRG).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom & Hev).
destruct OBJ0 as (STR & AT & HT & AC & HC & CAT & LITS & ROD & SSP).
destruct MID as (Ho & Hn & (Hno & Hlines & Hln & Hle)).
pose proof (PFA.pf_next_le (p_s v) o Ho) as HNL.
pose proof asan_consts as (C1 & _).
pose proof alloc_ceiling_lt as Hac.
split; [exact ROD|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [cbn [a8_ovf rc_refused]; destruct CNT as [CN1 _]; lia|].
  split; [lia|]. split; [reflexivity|].
  assert (HL : In F_bound PARSE_FILE_LITS)
    by (unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In]; repeat (first [left; reflexivity | right])).
  pose proof (LITS F_bound HL) as HLL.
  split; [unfold seg_spec.REFUSE_FORMATS; cbn [In]; repeat (first [left; reflexivity | right])|].
  split; [vm_compute; reflexivity|].
  split; [destruct HLL as (Hp & _); lia|]. split; [reflexivity|]. split; [exact HLL|].
  assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
      (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
      [(ly_stk_lo lyc, spZ regsc);
       (seg_spec.refusal_addr (p_c v) (length (rc_refusal (a8_ovf cf))),
        seg_spec.refusal_addr (p_c v) (length (rc_refusal (a8_ovf cf))) + seg_spec.RC_REFUSAL_LEN);
       (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]).
  { destruct (a6_heap_bounds B _ _ _ _ _ (p_c v) seg_spec.SEG_C_SIZE HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
      as (bc & mc & Hinc & Hcb1 & Hcb2 & _).
    destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
    constructor; [left; cbn [fst]; rewrite Hly; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
    constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
      unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
    constructor. }
  destruct (a6_buf_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE np name _ BASE0 eq_refl eq_refl Hxs Hxb HWl)
    as [HVA HLOC].
  split; [cbn [sa_va_args]; rewrite R13, R14; split; [exact HVA|];
          split; [cbn [sa_va_arg]; split; [lia | apply a6_w64_u; lia] | exact I]|].
  split; [cbn [refuse_va_locs]; rewrite R13; exact (conj HLOC I)|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- split.
  + unfold sa_room. unfold sa_room_n in Hroom. rewrite Hfrs. cbn [app length]. lia.
  + unfold EV_refuse. unfold EV_reac_segconf_parse_file in Hev. lia.
Qed.

Theorem a8_kf_main : forall n, HA_NEW B n -> HA_CLR B n ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  a8F B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8F) rX memc mdc) (a8Q B v cf nm o ln name).
Proof.
intros n HNEW HCLR v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (HC & HSL0 & HFD & HN1 & HR19).
unfold HA_NEW, H_NEW in HNEW.
pose proof HC as (HB & HM & (SRC & SNM & SCNT) & HSs & HIb & HLn & HR).
pose proof HB as (HCX & HFI & HOB & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPm & HSV & HFL & HFRM & HRF).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & _ & Hin5 & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof SRC as (bs & HBs & Henc).
pose proof Henc as (Lbs & L32 & _ & _ & _ & _ & _ & _ & ((OV0 & OV1) & _) & _).
unfold seg_spec.SEG_C_SIZE in Lbs.
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof HOB as (_ & _ & _ & _ & OCH & _).
destruct OCH as (bc & mc & Hinc & Hbc1 & Hbc2). unfold seg_spec.SEG_C_SIZE in Hbc2.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hinc) as (Hp16 & Hp4096 & Hpceil & Hpapp & _ & _ & Hkr).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
rewrite SPF in G1.
set (N := length (rc_seg cf)) in *.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by exact (a5_rg_get rX _ 2 _ HRF ltac:(cbn; tauto)).
destruct (a8r_seed_regs PF_A8F rX Wc memc v R2 ltac:(lia) G5) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
remember (Eimg (Ereg rX [])) as E eqn:HE. clear HE.
assert (E19 : ew E 19 = w64 (Z.of_nat N))
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact (a5_rg_get rX _ 19 _ HR19 ltac:(cbn; tauto))).
unfold cfg_at. change (w64 (BASE + PF_A8F)) with (Z_to_bv 64 (BASE + PF_A8F)).
(* 0x887f0: li a0, 0x20 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem]. apply awr_ok_nil. }
a8_md.
a8_kept_empty HFr KEEP1 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
(* 0x887f4: blt s3, a0, NEW *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n < 32: room for a new entry; NEW 0x8890c *)
  assert (HN32 : (N < 32)%nat).
  { rewrite (a8r_blt32 E 19 (Z.of_nat N) E19) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_NEW.
  { apply awr_ok_nil. }
  a8_md.
  a8_kept_empty HFr KEEP2 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) as KEEP3.
  pmkst HS.
  prreg HS (Z_to_bv 5 19 : bv 5) Q19.
  apply (HNEW fx v pos lyc Sc Wc _ _ _ cf nm o ln d np name). apply a8_new_ok.
  + apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v) (pf_s1 v) HC HJ);
      [exact KEEP3 | lia | left; lia |].
    a8_regs_kept HS EE.
  + apply (a8_sl_kept _ _ _ _ _ _ HSL0 KEEP3). intros ov Hov. cbn [In] in Hov. destruct Hov as [<- | []].
    cbn [fst]. lia.
  + exact HFD.
  + exact HN32.
  + rewrite Q19, E19. reflexivity.
- (* n = 32: no room; c->overflow++ and refuse(c, lineno, F_bound, name, 32) *)
  assert (HN32 : N = 32%nat).
  { rewrite (a8r_blt32 E 19 (Z.of_nat N) E19) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  unfold a8Q. rewrite (a8_step_full cf nm (ln + 1) name HFD ltac:(lia)).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_A8S.
  { apply awr_ok_nil. }
  a8_md.
  a8_kept_empty HFr KEEP2 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) as KEEP3.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rA _ ?mA _) ?dA) _ =>
    assert (KR1 : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 25; 26; 27] ->
      getr rA (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r));
    [ intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [a8r_kept HS EE|]); destruct Hr
    | assert (HCA : a8c B n v pos lyc Sc Wc rA mA dA cf nm o ln d np name);
      [ apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v) (pf_s1 v) HC HJ);
          [exact KEEP3 | lia | left; lia |];
        a8_regs_kept HS EE
      | ] ] end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (BASE + ?k)) _ _) _) _ =>
    change (BASE + k) with (BASE + PF_A8S) end.
  destruct (a8r_seedB n v pos lyc Sc Wc _ _ _ cf nm o ln d np name HCA) as [HS2 SHOK2].
  clear HS SHOK.
  lazymatch type of HS2 with st_ok_pi _ _ (a8r_E ?rT ?c0 ?ov0) _ _ =>
    destruct (a8r_E_facts rT c0 ov0 ltac:(lia) ltac:(lia)) as (HEI2 & EE2 & E32 & U32 & U33);
    remember (a8r_E rT c0 ov0) as E2 eqn:HE2; clear HE2 end.
  (* 0x887f8 .. 0x88834: check #30 (passed by the block's shadow entry), c->overflow++, the arguments, the call *)
  paj_run_tok RUN HS2 HJ SHOK2 Bspan.
  { unfold ss_a8r_B; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
    intros a Ha. unfold a8r_creg in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold seg_spec.RC_OVERFLOW in Ha.
    right; left. split.
    - exists (p_c v + seg_spec.RC_REFUSAL, p_c v + seg_spec.RC_OVERFLOW + 4).
      split; [unfold seg_spec.RC_PARSE_W; right; left; reflexivity|].
      cbn [fst snd]. unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW. lia.
    - exists bc, mc. split; [exact Hinc|]. lia. }
  a8_md.
  (* the memory at the call: only c->overflow's 4 bytes changed *)
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v + 13520 <= a < p_c v + 13524) ->
      aview SEGS H m2 a = aview SEGS H m1 a)
    by (intros x0 Hx0 Hn0;
        apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => p_c v + 13520 <= x < p_c v + 13524) HFr);
        [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin];
            [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr; lia|]);
          destruct Hin
        | exact Hx0 | exact Hn0 ]) end.
  clear HF HFr HG.
  (* the stored bytes: the chunk of the region on c after the run *)
  lazymatch type of HS2 with st_ok _ _ ?ssx _ =>
    let r := eval vm_compute in (nth 1 (ss_mem ssx) a8r_slots) in
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx _ 1 r HS2 ltac:(vm_compute; reflexivity)) as HRg end.
  cbn [ms_mem restrict] in HRg.
  destruct HRg as (_ & _ & _ & Hcs). cbn [YP09.r_chunks] in Hcs. apply Forall_inv in Hcs.
  cbn [YP09.r_base base_val] in Hcs. rewrite U32 in Hcs.
  assert (Hov1 : rc_overflow cf + 1 < 2 ^ 32) by (destruct SCNT as [_ Hcn]; lia).
  pose proof (a8r_stored E2 33 (rc_overflow cf) _ _ (p_c v) 13520 U33 OV0 Hov1 Hcs) as SV.
  clear Hcs.
  pmkst HS2.
  prreg HS2 (Z_to_bv 5 1 : bv 5) P1. prreg HS2 (Z_to_bv 5 10 : bv 5) P10. prreg HS2 (Z_to_bv 5 11 : bv 5) P11.
  prreg HS2 (Z_to_bv 5 12 : bv 5) P12. prreg HS2 (Z_to_bv 5 13 : bv 5) P13. prreg HS2 (Z_to_bv 5 14 : bv 5) P14.
  prreg HS2 (Z_to_bv 5 24 : bv 5) P24.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ _ _) _) _ =>
    assert (CR : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 25; 26; 27] ->
      getr rT (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r));
    [ intros r Hr; rewrite <- (KR1 r Hr); cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [a8r_kept HS2 EE2|]); destruct Hr | ] end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
    set (regsc := rT) in *; set (memT := mT) in *; set (mdT := dT) in * end.
  assert (KTc : forall a, 0 <= a < 2 ^ 64 ->
    ~ (p_c v + seg_spec.RC_OVERFLOW <= a < p_c v + seg_spec.RC_OVERFLOW + 4) -> rdW Wc memT a = rdW Wc memc a).
  { intros a Ha Hn. unfold seg_spec.RC_OVERFLOW in Hn. rewrite KT by (exact Ha || lia). apply KEEP3; [exact Ha | lia]. }
  destruct (a6_frame B v pos lyc Sc Wc rX memc mdc HFI) as (_ & HF4 & HFc & _ & _ & HFE).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hinc Hin5) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite HFE in Hsep. change (fs_frame_bytes 5) with 2048 in *.
  assert (KF : forall a, pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 -> rdW Wc memT a = rdW Wc memc a).
  { intros a Ha. change (fs_frame_bytes 5) with 2048 in Ha. apply KTc; [lia|]. unfold seg_spec.RC_OVERFLOW. lia. }
  assert (HSsT : sa_str (rdW Wc memT) np name).
  { apply (a8r_str_keep _ _ np name HSs). intros a Ha. apply KF. destruct HIb as [HI1 HI2]. unfold PF_O_BUF in *.
    unfold seg_spec.cstr_span in Ha. change (fs_frame_bytes 5) with 2048.
    clear - Ha HI1 HI2 G8. Z.div_mod_to_equations. lia. }
  assert (RCT : sa_rconf (rdW Wc memT) (p_c v) (a8_ovf cf)).
  { apply (a8r_rconf_store (rdW Wc memc) _ (p_c v) cf SRC Hov1); [|exact SV].
    intros i Hi Hn. apply KTc; [unfold seg_spec.SEG_C_SIZE in Hi; lia | lia]. }
  assert (HRGc : pf_rg regsc (a5_FI B v)).
  { apply (a8_rg_keep rX); [exact HRF|]. intros rv Hrv. apply CR. unfold a5_FI in Hrv. cbn [In] in Hrv.
    repeat (destruct Hrv as [<- | Hrv]; [cbn; tauto|]). destruct Hrv. }
  assert (HBT : pf_base B v pos lyc Sc Wc regsc memT mdT PF_SC_LINE).
  { apply (a8r_base_store v pos lyc Sc Wc rX memc mdc PF_SC_LINE regsc memT mdT
      (p_c v + seg_spec.RC_OVERFLOW) (p_c v + seg_spec.RC_OVERFLOW + 4) HB HJ);
      [unfold seg_spec.RC_OVERFLOW; lia | unfold seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE; lia | exact KTc | exact HRGc]. }
  (* the call's registers *)
  assert (C1 : getr regsc 1 = Z_to_bv 64 (BASE + PF_A8RR)).
  { change (getr regsc 1) with (getr regsc (Z_to_bv 5 1)). rewrite P1. reflexivity. }
  assert (C2 : getr regsc 2 = w64 (pf_s1 v)).
  { change (getr regsc 2) with (getr regsc (Z_to_bv 5 2)). rewrite (CR 2 ltac:(cbn; tauto)).
    exact (a5_rg_get rX _ 2 _ HRF ltac:(cbn; tauto)). }
  assert (C3 : getr regsc 3 = w64 (as_gp B)).
  { change (getr regsc 3) with (getr regsc (Z_to_bv 5 3)). rewrite (CR 3 ltac:(cbn; tauto)).
    exact (a5_rg_get rX _ 3 _ HRF ltac:(cbn; tauto)). }
  assert (C4 : getr regsc 4 = w64 (as_tp B)).
  { change (getr regsc 4) with (getr regsc (Z_to_bv 5 4)). rewrite (CR 4 ltac:(cbn; tauto)).
    exact (a5_rg_get rX _ 4 _ HRF ltac:(cbn; tauto)). }
  assert (C8 : getr regsc 8 = w64 (pf_sp0 v)).
  { change (getr regsc 8) with (getr regsc (Z_to_bv 5 8)). rewrite (CR 8 ltac:(cbn; tauto)).
    exact (a5_rg_get rX _ 8 _ HRF ltac:(cbn; tauto)). }
  assert (C10 : getr regsc 10 = w64 (p_c v)).
  { change (getr regsc 10) with (getr regsc (Z_to_bv 5 10)). rewrite P10. exact E32. }
  assert (C11 : getr regsc 11 = w64 (ln + 1)).
  { change (getr regsc 11) with (getr regsc (Z_to_bv 5 11)). rewrite P11.
    rewrite (EE2 26%nat (Z_to_bv 5 26) eq_refl), (KR1 26 ltac:(cbn; tauto)).
    apply (a5_rg_get rX _ 26 _ HR). unfold PF_RM. cbn [app In]. tauto. }
  assert (C12 : getr regsc 12 = w64 (seg_litA_rc F_bound)).
  { change (getr regsc 12) with (getr regsc (Z_to_bv 5 12)). rewrite P12.
    change 308%nat with (A_OBJ 67). exact (a8r_lit _ HEI2). }
  assert (C13 : getr regsc 13 = w64 np).
  { change (getr regsc 13) with (getr regsc (Z_to_bv 5 13)). rewrite P13.
    rewrite (EE2 25%nat (Z_to_bv 5 25) eq_refl), (KR1 25 ltac:(cbn; tauto)).
    apply (a5_rg_get rX _ 25 _ HR). cbn [app In]. tauto. }
  assert (C14 : getr regsc 14 = w64 32).
  { change (getr regsc 14) with (getr regsc (Z_to_bv 5 14)). rewrite P14. reflexivity. }
  assert (C24 : getr regsc (Z_to_bv 5 24) = w64 (p_c v)) by (rewrite P24; exact E32).
  pose proof (a8_sp B v HCX) as (S1' & S2' & S3' & S4' & S5').
  pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
  assert (Csp : spZ regsc = pf_s1 v).
  { unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
  (* VERIFY rule 1j-bis at 0x88834 *)
  destruct (refuse_site_ok_88834 n v pos lyc Sc Wc regsc memT mdT cf o ln d np name regsc HBT HM RCT SCNT HSsT HIb
    C2 C13 C14) as (ROD & RPRE & ROOM & EV).
  pose proof RPRE as (_ & _ & _ & _ & _ & _ & HLN & _).
  assert (LF : seg_litA_rc F_bound = 136640) by (vm_compute; reflexivity).
  assert (Hf64 : 0 <= seg_litA_rc F_bound < 2 ^ 64) by (rewrite LF; lia).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  destruct (a5_chain B v pos lyc Sc Wc regsc memT mdT PF_SC_LINE HBT) as [ch1 HCH].
  rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
  eapply SRr_bind.
  { eapply (cl_callSF (fx := fx) B LAWS Wc regsc memT _ STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdT 0
      STK_refuse (refuse_W (p_c v) (a8_ovf cf)) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_A8RR)) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         sa_rconf (rdW W2 mem2) (p_c v) (refuse (a8_ovf cf) (ln + 1) F_bound [AS name; AI 32]) /\
         sa_noalloc B lyc Sc ly2 S2) HJ).
    - rewrite Csp. lia.
    - exact S1d.
    - lia.
    - rewrite SRF. lia.
    - rewrite SRF, SPF. lia.
    - exact C3.
    - exact C4.
    - exact C1.
    - apply ret_ok_codeptr_v; [unfold PF_A8RR, AF_reac_segconf_parse_file; lia | reflexivity].
    - rewrite unsigned_lit_small by (unfold PF_A8RR, AF_reac_segconf_parse_file; lia).
      unfold PF_A8RR, AF_reac_segconf_parse_file. lia.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
    - intros HPRE1. eapply SRr_mono.
      { exact (REF fx lyc Sc Wc regsc memT mdT ch1 (p_c v) (ln + 1) (seg_litA_rc F_bound) (ln + 1) (a8_ovf cf)
          F_bound [AS name; AI 32] HPRE1 ROD C10 Hc64 C11 ltac:(lia) C12 Hf64 RPRE ROOM EV). }
      cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
      split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
    - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
      apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
      unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *. lia. }
  (* back at 0x88838, at the FP state fx1 refuse returned *)
  cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
  unfold pf_postm, PF_POSTr.
  eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
  replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
  destruct HNA2 as (HP2b & Hly2 & HS2e).
  pose proof (a6_keeps_refuse B v pos lyc Sc Wc regsc memT mdT PF_SC_LINE (a8_ovf cf) ly2 S2 W2 mem2 md2 EV_refuse
    HBT HJc2 HP2b) as HK.
  (* refuse's post gives only its journal; the journal keeps an image byte only when it is not in
     as_owned_static B (YCbq.v:479), and whether the GOT word 0xa36d8 and the guard 0x5ff078 are owned statics is a
     record fact that arrives with listing stage 2 (SegRecCells.seg_rec_cells); arodata_okP after refuse needs
     pa_relro_img, which is VRO. So SSPX and VRO are used here, and only here. *)
  assert (HB2 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_LINE).
  { apply (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc regsc memT mdT PF_SC_LINE ly2 S2 W2 regs2
      mem2 md2 HBT Hfx1 HJ2 Hly2 HS2e HP2b HK).
    intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
  pose proof HM as (Ho & _).
  assert (HINV2 : INV_CLR (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2
    (refuse (a8_ovf cf) (ln + 1) F_bound [AS name; AI 32]) nm o ln d).
  { split; [exact HB2|]. split; [exact HM|]. split.
    - split; [exact HRC2|]. split.
      + destruct HK as (_ & _ & _ & K4). apply (a6_nm_move v pos (rdW Wc memT) _ nm).
        * exact (a6_nm_move v pos (rdW Wc memc) _ nm SNM KF).
        * intros a Ha. apply K4. left. exact Ha.
      + apply (a8r_cnt cf (length (skipn o (p_s v)))); [exact (PFA.pf_next_skipn_lt (p_s v) o Ho) | exact SCNT].
    - apply (a5_rg_pres regsc regs2 _ HP2).
      + unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
      + unfold pf_rg, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        * rewrite (CR 18 ltac:(cbn; tauto)). exact (a5_rg_get rX _ 18 _ HR ltac:(cbn; tauto)).
        * exact C24.
        * rewrite (CR 27 ltac:(cbn; tauto)). exact (a5_rg_get rX _ 27 _ HR ltac:(cbn; tauto)).
        * rewrite (CR 21 ltac:(cbn; tauto)). apply (a5_rg_get rX _ 21 _ HR). unfold PF_RM. cbn [app In]. tauto.
        * rewrite (CR 26 ltac:(cbn; tauto)). apply (a5_rg_get rX _ 26 _ HR). unfold PF_RM. cbn [app In]. tauto. }
  exact (a8r_ret (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 _ nm o ln d (HCLR fx1) HINV2).
Qed.
End e.
End f.
End d.
