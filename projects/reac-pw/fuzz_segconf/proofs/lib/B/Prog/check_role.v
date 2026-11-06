(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of rec_code_declared on fuzz_command.asan, in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (cmpPixel's leaf walk): a seed lemma at the entry, then the executor's run/branch loop to every return. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_code_declared.v, with its module paths, module names and numbers changed; 242 of its 328 lines of code are new or changed and 226 lines of the source are left out. *)
(* the image-B port of lib/A/Prog/check_role.v (commit e79686f8d801): the walk of check_role on
   fuzz_segconf.asan-ubsan (image B, 0x870f8 = BASE + AF_check_role, 148 bytes, 37 instructions), against
   lib/B/Prog/check_role_c.v's check_role_contract (image B's copy of lib/A/Prog/check_role_c.v, FINAL 6f783602b5e3).
   ADAPTED: image B's code is image A's 34 instructions in order (other addresses: the GOT word 0xa3210, the abort arm
   0x8715c, the error paths) plus UBSan's alignment test at the entry, `andi a3,a2,3; bnez a3` (0x87100, 0x87104) to
   the trap `unimp` 0x87164. The run: the 16-byte frame (`addi sp,sp,-16; sd ra,8(sp)`), the alignment test (not
   taken: atom 12, want, has the fact PTR 2, alignment 2 ^ 2, from the contract's want mod 4 = 0; the executor decides
   the branch from it), the shadow base through the GOT word A_OBJ 0 (0xa3210) and the cell A_OBJ 12 (0xac7b8), the
   check of want + 0x14 (removed by the tokens: the shadow entry [want + 16, want + 24) is addressable by the
   contract's sa_addr), `lw` of want->role_set, `bne a0, a3` to the abort arm (dead: a0 = got_set = role_set),
   `beqz a0` (o = None returns), the check of want + 0x10, `lw` of want->role, `bne a1, a0` to the abort arm (dead:
   a1 = r = role, below 2^31), the return 0x87158. The trap `unimp` 0x87164 is reached only by the alignment branch
   0x87104 (the word before it is `jal abort`, on the dead abort arm, and abort does not return).
   Image-B number: the stack window SegInstB.STK_check_role (16, the frame `addi sp,sp,-16` at 0x870f8; image B's
   instance file lib/B/Prog/SegInstB.v); the entry stays the listing term BASE + AF_check_role. The post's sa_kept
   clause (footprint none): each run stretch's frame_of fact gives, by kept_of_frame, that every byte outside
   [sp - 16, sp) reads as before the stretch; the facts of the stretches compose from the entry memory to the return
   memory. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YN2e.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaSB PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase check_role_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* `lw` sign-extends bit 31: a value below 2^31 comes back as itself *)
Lemma crl_U_sx : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. cbv iota.
assert (H32 : v mod 2 ^ Z.of_N 32 = v) by (apply Z.mod_small; change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
rewrite H32.
assert (HW : bv_swrap 32 v = v).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia. }
rewrite HW. apply zcanon_id. unfold M64. lia.
Qed.
Lemma crl_nth_firstn : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
induction l as [|x l IH]; intros n i d Hi; destruct n as [|n]; try lia; cbn [firstn].
- destruct i; reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma crl_nth_skipn : forall (l : list byte) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
induction l as [|x l IH]; intros [|j] i d; cbn [skipn Nat.add]; try reflexivity.
- destruct i; reflexivity.
- cbn [nth]. apply IH.
Qed.
(* a 4-byte field of a byte block read through the reader, as the restricted memory holds it *)
Lemma crl_fld4 : forall segs H mem a (bs : list byte) off v,
sa_bytes (aview segs H mem) a bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
seg_spec.fldz off 4 bs = Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 v)) -> 0 <= v < 2 ^ 32 ->
YI04.val_mem segs (mrestrict H mem) (a + off) 4 v.
Proof.
intros segs H mem a bs off v HB Ho Hl HF Hv k Hk.
rewrite unsigned_lit_small in HF by lia.
assert (Hi : (Z.to_nat off + k < length bs)%nat) by lia.
specialize (HB (Z.to_nat off + k)%nat Hi).
replace (a + Z.of_nat (Z.to_nat off + k)) with (a + off + Z.of_nat k) in HB by lia.
unfold aview in HB.
destruct (mbyte segs (mrestrict H mem) (a + off + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in HB; [|discriminate HB].
injection HB as Hb. f_equal.
rewrite (le_byte_small v 4 k)
  by (first [split; [lia|]; eapply Z.lt_le_trans; [apply (proj2 Hv)|]; apply Z.pow_le_mono_r; lia | lia]).
apply bv_eq.
assert (HN : nth (Z.to_nat off + k) bs ZB0 = nth k (Z_to_le_bytes 4 v) ZB0).
{ rewrite <- HF. unfold seg_spec.fldz, seg_spec.fld. rewrite crl_nth_firstn by lia. rewrite crl_nth_skipn. reflexivity. }
assert (Hn : nth k (Z_to_le_bytes 4 v) ZB0 = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)))
  by (apply nth_error_nth; exact (YN2e.Z_to_le_bytes_nth 4 v k Hk)).
rewrite Hb, HN, Hn. reflexivity.
Qed.
(* the contract's sa_kept clause, carried along the run: it holds of the entry memory, and a stretch that writes
   only inside the window keeps it *)
Lemma crl_kept_refl : forall segs (W : world segs) mem regs STK (E : Z -> Prop), sa_kept segs W mem W mem regs STK E.
Proof. intros segs W mem regs STK E a _ _ _. reflexivity. Qed.
Lemma crl_kept_step : forall segs (W : world segs) mem m0 m1 regs STK (E : Z -> Prop),
sa_kept segs W mem W m0 regs STK E ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) m1 a = aview segs (w_H W) m0 a) ->
sa_kept segs W mem W m1 regs STK E.
Proof. intros segs W mem m0 m1 regs STK E K0 K1 a Ha Hn He. rewrite (K1 a Ha Hn). exact (K0 a Ha Hn He). Qed.

(* the symbolic state at the entry. Atoms: 0..31 the registers at the entry (a0 = got_set atom 10, a1 = got atom
   11, a2 = want atom 12, sp atom 2), 32 the shadow base 0x7fff8000, 33 want->role's value (ms_role g), 34
   want->role_set's value (1 or 0); A_OBJ 0 / A_OBJ 12 the GOT word 0xa3210 and the cell 0xac7b8 (image B's
   SegAddr seg_objs, entries 0 and 12; SegRo RO_ptr_a3210 holds 0xac7b8). Atom 12's fact PTR 2 (alignment 2 ^ 2,
   from want mod 4 = 0) decides UBSan's alignment test `andi a3,a2,3; bnez a3` (0x87104) not taken.
   Regions: the 16-byte frame; the GOT word and the cell (read-only); the two 4-byte fields of the mseg entry at
   want + 16 and want + 20 (read-only). The one shadow entry [want + 16, want + 24) removes both inline checks. *)
Definition crl_Bx : sv := SOff 32 0.
Definition crl_SH : list shent := [mkSHE 12 16 24].
Definition crl_want : YP09.region :=
YP09.mkRegion (Some 12%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SOff 34 0))].
Definition crl_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32; crl_want].
Definition crl_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (12%nat, PTR 2); (32%nat, mkAF SB SB 0);
  (33%nat, mkAF 0 (2^31 - 1) 0); (34%nat, mkAF 0 1 0) ] [] [].
Definition ss_crl : sstate := mkSS AF_check_role sr_atoms crl_regions None crl_facts.
Definition crl_extra (role rs : Z) : list word := map (Z_to_bv 64) [SB; role; rs].

(* U of a value the run builds from atoms of known value (a register, a sign-extended `lw` of a field, a literal) *)
Ltac crl_atom Ex n :=
  match goal with
  | H0 : ew _ n = Z_to_bv 64 ?v |- _ =>
      let H := fresh "Hx" in
      assert (H : ew Ex n = Z_to_bv 64 v)
        by (first [ exact H0
                  | cbn [ew ewset extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
                    rewrite ?ew_ewset_other by lia; exact H0 ]);
      first [ rewrite (crl_U_sx Ex n v H) by lia | rewrite (U_atom Ex n v H) by lia ]; clear H
  end.
Ltac crl_Us :=
  repeat match goal with
  | |- context [U ?Ex (SExt true 32 (SOff ?n 0))] => crl_atom Ex n
  | |- context [U ?Ex (SOff ?n 0)] => crl_atom Ex n
  | |- context [U ?Ex (SLit ?z)] => rewrite (U_lit Ex z) by lia
  end.
(* a branch arm the values make impossible *)
Ltac crl_dead :=
  exfalso;
  lazymatch goal with Hc : branch_taken _ (sv_denot _ _) (sv_denot _ _) = _ |- _ =>
    revert Hc; first [rewrite branch_ne_U | rewrite branch_eq_U]; crl_Us;
    lazymatch goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) as [Hq|Hq] end;
    cbn [negb]; intros Hc; first [discriminate Hc | lia]
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Definition crl_E (regs : bvmap 5 word) (role rs : Z) : env := Eimg (Ereg regs (crl_extra role rs)).
Section h.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma crl_entry : forall ly S W (regs : bvmap 5 word) mem md ch want (g : mseg),
afn_pre SEGS B SegInstB.STK_check_role ly S W regs mem md ch ->
getr regs 12 = w64 want -> 0 <= want < 2 ^ 64 -> want mod 4 = 0 ->
sa_mseg (aview SEGS (w_H W) mem) want g -> sa_heap B ly S want seg_spec.MSEG_SIZE ->
sa_addr (aview SEGS (w_H W) mem) want seg_spec.MSEG_SIZE ->
st_ok_pi SEGS VAL (crl_E regs (ms_role g) (if ms_role_set g then 1 else 0)) ss_crl
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_role)) mem (seg_rom SEGS)))
/\ sh_ok SEGS crl_Bx crl_SH (crl_E regs (ms_role g) (if ms_role_set g then 1 else 0)) (mrestrict (w_H W) mem).
Proof using TL LAWS HBgot HBcell.
intros ly S W regs mem md ch want g HPRE H12 R12 Hal4 HMS HHP HAD.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SegInstB.STK_check_role = 16) by reflexivity. rewrite WS in Hstk0, Hslo, Hbot, Hpres.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as O0. pose proof (pa_obj_img 12 ltac:(lia)) as O12.
pose proof (pal_got_cell B TL) as GC. unfold kImgEnd in O0, O12.
(* the mseg's block: a live heap block, off the image and below the stack *)
destruct HHP as (b & m & Hin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & Hbm).
assert (Hoff : off_img b (req_size m)) by (eapply blk_off_imgP; eassumption). unfold off_img in Hoff.
pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
unfold seg_spec.MSEG_SIZE in Hb2.
(* the two fields *)
destruct HMS as (bs & HBS & HE). destruct HE as (Hlen & _ & [Hu Hr31] & Hrs & _).
assert (HL : Z.of_nat (length bs) = 256) by (rewrite Hlen; reflexivity).
assert (Rrs : 0 <= (if ms_role_set g then 1 else 0) < 2 ^ 32) by (destruct (ms_role_set g); lia).
assert (RD1 : val_mem SEGS (mrestrict (w_H W) mem) (want + 16) 4 (ms_role g))
by (apply (crl_fld4 SEGS (w_H W) mem want bs 16 (ms_role g) HBS); [lia | lia | exact (proj2 Hu) | exact (proj1 Hu)]).
assert (RD2 : val_mem SEGS (mrestrict (w_H W) mem) (want + 20) 4 (if ms_role_set g then 1 else 0))
by (apply (crl_fld4 SEGS (w_H W) mem want bs 20 _ HBS); [lia | lia | exact Hrs | exact Rrs]).
pose proof (proj1 Hu) as Rrole.
rewrite restrict_mkst_fx.
set (E := crl_E regs (ms_role g) (if ms_role_set g then 1 else 0)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (crl_extra (ms_role g) (if ms_role_set g then 1 else 0))) n)
by (intros n Hn; subst E; unfold crl_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 want)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (ms_role g)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (if ms_role_set g then 1 else 0))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold crl_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold crl_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_crl. apply pa_entry_st_ok_full.
  + subst E. unfold crl_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold crl_regions, crl_want, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 crl_Bx SB);
      [unfold crl_Bx; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 12%nat want E12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ want 16 4 (SOff 33 0) (ms_role g));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact RD1.
      -- apply (chunk_ok_val SEGS E _ want 20 4 (SOff 34 0) (if ms_role_set g then 1 else 0));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact RD2.
  + apply pairwise_disjoint_of_extents. unfold crl_regions, crl_want, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12), (VB 12%nat want E12) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - Hslo Hshi H47 C1 Hceil Hbceil Hb1 Hb2 Hreq Hoff O0 O12 GC Hb4096.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [crl_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E12, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    clear - Hal16 Hslo Hshi H47 C1 Hceil Hbceil Hb1 Hb2 Hreq Hb4096 Hal4 Rrole Hr31 Rrs. unfold SB.
    repeat split; first [lia | reflexivity | destruct (ms_role_set g); lia].
- unfold sh_ok, crl_SH. constructor; [|constructor].
  destruct HAD as (_ & _ & HAM & HRA & _).
  apply (shent_ok_of_range SEGS (w_H W) mem E crl_Bx 12 want seg_spec.MSEG_SIZE want 16 24 HRA).
  + unfold U, crl_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  + lia.
  + unfold seg_spec.MSEG_SIZE. lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, seg_spec.MSEG_SIZE in *. lia.
Qed.

(* The walk: the executor runs from the entry to each compare (the alignment test 0x87104 it decides from atom 12's
   fact, so no arm to the trap `unimp` 0x87164 is made); each split, the arm to the abort site (0x8715c) and the arm
   the got_set flag excludes, is refuted from the atoms' values; the run ends at the return 0x87158.
   Each stretch's frame fact extends KP, the sa_kept clause from the entry memory to the stretch's end. *)
Theorem check_role_walk : check_role_contract SEGS B (BASE + AF_check_role) SegInstB.STK_check_role.
Proof using TL LAWS HBgot HBcell RUN BR RET.
unfold check_role_contract.
intros ly S W regs mem md ch gotset got want o g HPRE H10 R10 H11 R11 H12 R12 HCP Hev.
unfold check_role_pre in HCP. destruct HCP as (Hal4 & HMS & HHP & HAD & Hgs & Hgot & Hok).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
assert (Rrole : 0 <= ms_role g < 2 ^ 31).
{ destruct HMS as (bs & _ & (_ & _ & [[Hu _] Hr31] & _)). lia. }
destruct (crl_entry ly S W regs mem md ch want g HPRE H12 R12 Hal4 HMS HHP HAD) as [HS SHOK].
pose proof (ajournal_init SEGS B SegInstB.STK_check_role [] ly S W regs mem md ch HPRE) as HJ.
pose proof (crl_kept_refl SEGS W mem regs SegInstB.STK_check_role (fun _ => False)) as KP.
assert (HSTK : SegInstB.STK_check_role = 16) by reflexivity.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
unfold YK0s.ret_ok in Hra.
remember (crl_E regs (ms_role g) (if ms_role_set g then 1 else 0)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold crl_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (crl_extra (ms_role g) (if ms_role_set g then 1 else 0))) n)
by (intros n Hn; subst E; unfold crl_E; apply Eimg_low; exact Hn).
assert (E0 : ew E 0 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 0 0%bv eq_refl); apply getr_zero).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 gotset)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 got)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E33 : ew E 33 = Z_to_bv 64 (ms_role g)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (if ms_role_set g then 1 else 0))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (crl_extra (ms_role g) (if ms_role_set g then 1 else 0))) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. try change (w64 (BASE + AF_check_role)) with (Z_to_bv 64 (BASE + AF_check_role)).
(* the atoms' values in each case of the reader's answer *)
destruct o as [r|]; cbv beta iota in Hgs, Hgot, Hok;
[ destruct Hgot as [Hgr Hr31]; subst got;
  apply andb_prop in Hok; destruct Hok as [Hrs1 Hrr]; apply Z.eqb_eq in Hrr;
  rewrite Hrs1 in E34; change (if true then 1 else 0) with 1 in E34;
  rewrite Hgs in E10; rewrite <- Hrr in E33; clear Hgs Hrs1
| apply negb_true_iff in Hok; rewrite Hok in E34; change (if false then 1 else 0) with 0 in E34;
  rewrite Hgs in E10; clear Hgs ].
all: clear HMS HHP HAD.
all:
let leaf_ret := idtac;
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R1 := fresh "R1" in let HAEx := fresh "HAEx" in
prreg HS (1%bv : bv 5) R1;
assert (HAEx : env_agree 32 (Ereg regs (crl_extra (ms_role g) (if ms_role_set g then 1 else 0))) Ex)
by (first [exact HAE | destruct HAE as [HA HD]; split;
[intros n Hn; rewrite !ew_ewset_other by lia; apply HA; exact Hn | rewrite !ed_ewset; exact HD]]);
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold apost_base;
eexists _, _, _, _, _;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs _ HS); [exact HAEx | vm_compute; reflexivity]|];
(* the window clause: KP; no call, no frame of the side stack: the run keeps the layout and the allocator state *)
split; [exact KP|];
unfold sa_noalloc; split; [apply Permutation_refl | split; [reflexivity | exists (st_fs S); destruct S; reflexivity]]
end in
(* a stretch's frame fact: it wrote only the windows of its regions, of which the frame [sp - 16, sp) is the one
   non-empty window; so KP extends to the stretch's end memory *)
let keep := idtac;
lazymatch goal with HFr : frame_of ?Ex _ (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
let Uspx := fresh "Uspx" in let KR := fresh "KR" in let KP2 := fresh "KP" in
assert (Uspx : bv_unsigned (ew Ex 2) = spZ regs) by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp);
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SegInstB.STK_check_role <= a < spZ regs) ->
  aview SEGS H m1 a = aview SEGS H m0 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
    apply (kept_of_frame (segs := SEGS) Ex _ H m0 m1 (fun x => spZ regs - SegInstB.STK_check_role <= x < spZ regs) HFr);
    [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
      let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
      intros b wlo whi x Hin Hrr; vm_compute in Hin;
      repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
              [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspx in Hrr; cbv beta; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]);
pose proof (crl_kept_step _ _ _ _ _ _ _ _ KP KR) as KP2; clear KP KR Uspx; rename KP2 into KP
end in
let rec go n := idtac;
lazymatch n with Datatypes.O => fail "go: out of fuel" | Datatypes.S ?m =>
lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |];
keep;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ =>
tryif is_var mdq then idtac else (let mdv := fresh "mdv" in set (mdv := mdq) in *; clearbody mdv) end;
srr_norm_model;
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM crl_Bx crl_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K crl_Bx Bspan crl_SH (start K crl_Bx Bspan crl_SH ss) end in
lazymatch why with
| SR_jalr _ => leaf_ret
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' Bspan; [first [crl_dead | go m] | first [crl_dead | go m]]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end end in
go 10%nat.
Qed.
End h.
End f.
End d.
About check_role_walk.
Print Assumptions check_role_walk.
