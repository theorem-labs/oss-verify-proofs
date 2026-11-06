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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 824 of its 867 lines of code are new or changed and 410 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: piece PA10_B of segment A10b of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_a10b_k.v): `pa10_b_ok : PA10_B B`, i.e. HA_JOIN n -> HA_ROLEV n -> H_INTENT n.
   proves no function (kind: segment lemma); the function is reac_segconf_parse_file (image-A 0x87a78), reuse
   verdict none (briefs/g3-lookup.md). Segment A10b's proof, by the G3 walk owner, 2026-10-30.

   THE CODE (dis/reac_segconf_parse_file.fuzz_segconf.asan.s; listing offsets from BASE + AF = 0x87a78):
     0x88450 a0 = hi(.), a1 = A_OBJ 55 (S_auto), a2 = 5, a0 = s3 (low)       0x88460 bcmp     ret B_RET0
     0x88464 beqz a0 -> 0x884f0 (s3 = 0; j ROLEV)
     0x88468 a1 = A_OBJ 56 (S_master), a2 = 7, a0 = s3                         0x88478 bcmp     ret B_RET1
     0x8847c beqz a0 -> 0x885a0 (s3 = 1; j ROLEV)
     0x88480 a1 = A_OBJ 57 (S_slave), a2 = 6, a0 = s3                          0x88490 bcmp     ret B_RET2
     0x88494 beqz a0 -> 0x8879c (s3 = 2; j ROLEV)
     0x88498 a1 = A_OBJ 58 (S_tap), a2 = 4, a0 = s3                            0x884a8 bcmp     ret B_RET3
     0x884ac beqz a0 -> 0x8883c (s3 = 3; falls into ROLEV)
     0x884b0 a3 = s3, a1 = A_OBJ 59 (S_box), a2 = 4, s3 = 4, a0 = a3           0x884c8 bcmp     ret B_RET4
     0x884cc beqz a0 -> ROLEV (s3 = 4)
     0x884d0 a2 = A_OBJ 60 (F_badrole), a0 = s8 = c, a1 = s10 = ln + 1, a3 = [s1 + 0x50] = cur_name, a4 = s9 = vp
     0x884e8 refuse ret PF_REFRET 0x884ec: j JOIN.
   THE FORM. Each stretch between two calls is one plain symbolic run (PaLibF / PaCallRun) from a seed b_ss
   over the registers (atoms 0..31 = the registers, atom 32 = the cur_name pointer of slot 0x50, read-only
   region b_slot on s1's atom 9), so the run writes no memory. A bcmp call is YCbq.aj_bcmp_at (b_bcmp_step), its
   result read through pf_a10b_f.a10b_cmp_lit; the cut's facts are carried across it by its own keep clause
   (window [s1 - 2 ESTACK, s1)). The refuse call is PaFx.cl_callSF with refuse_contract; after it the JOIN cut
   is rebuilt (b_join) and the walk goes on at the returned FP state (b_after_refuse).
   HELPER FILES (same lane): pf_a10b_b2.v (the cut facts across a bcmp call, aj_bcmp_at's premises),
   pf_a10b_b3.v (refuse_pre and cl_callSF's premises at 0x884e8), pf_a10b_b4.v (the JOIN cut after refuse).
   SECTION HYPOTHESES of pa10_b_ok, in order: ABCMP, REFUSE (the two callees), SIGP, OBJ (the listing's call
   target and literal atoms), SSPX, VRO (forced only by pf_a6_k.a6_base_move after the refuse call). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegGlob SegInstA SegObj refuse_c reac_segconf_parse_file_c pf_pieces pf_a10b_k pf_a10b_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_k pf_a6_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a10b_b2 pf_a10b_b3 pf_a10b_b4.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The listing offsets of the five bcmp returns (BASE + AF_reac_segconf_parse_file = 0x87a78) *)
Definition B_RET0 : Z := AF_reac_segconf_parse_file + 0x9ec.  (* 0x88464 *)
Definition B_RET1 : Z := AF_reac_segconf_parse_file + 0xa04.  (* 0x8847c *)
Definition B_RET2 : Z := AF_reac_segconf_parse_file + 0xa1c.  (* 0x88494 *)
Definition B_RET3 : Z := AF_reac_segconf_parse_file + 0xa34.  (* 0x884ac *)
Definition B_RET4 : Z := AF_reac_segconf_parse_file + 0xa54.  (* 0x884cc *)

(** ** The seed: registers as atoms 0..31, atom 32 the word of slot 0x50 (cur_name's address), read-only *)
Definition b_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x50 0x58 0x50 0x50 [YP09.mkChunk 0x50 (CVal 8 (SOff 32 0))].
Definition b_ss (pc : Z) : sstate := mkSS pc sr_atoms [b_slot] None (mkFacts [] [] []).
(* the callee-saved registers but s3: no run of this piece writes them *)
Definition B_CS : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma b_words_len : forall w, In w m_file_c.MF_ROLE_WORDS -> (length w <= 6)%nat.
Proof.
intros w Hw. unfold m_file_c.MF_ROLE_WORDS in Hw.
repeat (destruct Hw as [<- | Hw]; [vm_compute; lia|]). destruct Hw.
Qed.
Lemma b_words_in : forall j w, nth_error m_file_c.MF_ROLE_WORDS j = Some w -> In w m_file_c.MF_ROLE_WORDS.
Proof. intros j w H. exact (nth_error_In _ _ H). Qed.

(* register lists *)
Lemma b_rg_keep : forall (rX rX' : bvmap 5 word) L,
  (forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q)) ->
  Forall (fun rv => acallee_saved (fst rv) /\ fst rv <> 19) L -> pf_rg rX L -> pf_rg rX' L.
Proof.
intros rX rX' L HK HC H. unfold pf_rg in *. rewrite Forall_forall in *.
intros rv Hin. destruct (HC rv Hin) as [H1 H2]. rewrite (HK _ H1 H2). exact (H rv Hin).
Qed.
Ltac b_forall :=
  try unfold a5_FI; try unfold PF_RM; cbn [app];
  repeat (apply Forall_cons; [cbn [fst]; unfold acallee_saved; lia|]); apply Forall_nil.
Lemma b_pres_keep : forall (rX rX' : bvmap 5 word), aregs_preserved rX rX' ->
  forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q).
Proof. intros rX rX' HP q Hq _. exact (HP q Hq). Qed.
Lemma b_kept_keep : forall (rX rX' : bvmap 5 word),
  (forall r, In r (map (Z_to_bv 5) B_CS) -> getr rX' r = getr rX r) ->
  forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q).
Proof.
intros rX rX' HK q Hq H19. apply HK. apply in_map. unfold B_CS, acallee_saved in *. cbn [In]. lia.
Qed.

(* reading a register of a symbolic state *)
Ltac b_greg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
      pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
      cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
      pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
      cbn [ms_regs restrict mkst] in H
  end.
(* the run's writes: b_ss has one read-only region *)
Ltac b_awr := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* the call offset o = s1 - sp0 of every call of this piece *)
Lemma b_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
apply Z.mod_divide; [lia|]. destruct Ha as [p Hp]. destruct Hb as [q Hq]. exists (2 * p - q). lia.
Qed.
Lemma b_o_bounds : forall sp0 s1, sp0 mod 16 = 0 -> s1 mod 32 = 0 -> sp0 - 0x160 < s1 <= sp0 - 0x140 ->
  (s1 - sp0) mod 16 = 0 /\ sp0 - 336 <= s1.
Proof.
intros sp0 s1 H0 H1 H2. pose proof (b_mod16 s1 sp0 H1 H0) as H3. split; [exact H3|].
apply Z.mod_divide in H3; [|lia]. destruct H3 as [k Hk]. lia.
Qed.

(** ** The environment of the seed *)
Section x. Context {rc : YM05.RunCeil} {PI : PAImg seg_listing}.
#[local] Notation VAL := (@pa_val _ seg_listing PI).
Definition b_E (rX : bvmap 5 word) (cn : Z) : env := Eimg (Ereg rX [Z_to_bv 64 cn]).
Lemma b_E_img : forall rX cn, img_env VAL A_LIM (b_E rX cn).
Proof. intros. unfold b_E. apply Eimg_env. Qed.
Lemma b_E_agree : forall rX cn, env_agree 32 (Ereg rX [Z_to_bv 64 cn]) (b_E rX cn).
Proof.
intros rX cn. split; [intros n Hn; unfold b_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.
Lemma b_den_reg : forall rX cn n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  sv_denot (b_E rX cn) (SOff n 0) = getr rX r.
Proof.
intros rX cn n r Hn. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. unfold b_E.
apply ew_Eimg_Ereg_nat. exact Hn.
Qed.
Lemma b_beqz : forall rX cn b,
  branch_taken BC_EQ (sv_denot (b_E rX cn) (SOff 10 0)) (sv_denot (b_E rX cn) (SLit 0)) = b ->
  (getr rX 10 = w64 0 <-> b = true).
Proof.
intros rX cn b Hc. rewrite branch_eq_U in Hc. unfold U in Hc.
rewrite (b_den_reg rX cn 10 10 eq_refl) in Hc. cbn [sv_denot] in Hc.
subst b. split; intros H.
- rewrite H. reflexivity.
- apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity.
Qed.
End x.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The seed lemma *)
Lemma b_seed : forall (W : world SEGS) (rX : bvmap 5 word) memc pc s1 cn,
  getr rX (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 0x58 <= 2 ^ 64 -> 0 <= cn < 2 ^ 64 ->
  rdword (rdW W memc) (s1 + 0x50) = Some cn ->
  st_ok_pi SEGS VAL (b_E rX cn) (b_ss pc) (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros W rX memc pc s1 cn H9 Hs0 Hs1 Hcn Hw.
assert (E9 : ew (b_E rX cn) 9 = Z_to_bv 64 s1)
  by (unfold b_E; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E32 : ew (b_E rX cn) 32 = Z_to_bv 64 cn)
  by (unfold b_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
rewrite restrict_mkst_fx. unfold b_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, b_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ s1 0x50 8%N (SOff 32 0) cn).
  + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
  + change (8 * Z.of_N 8) with 64. lia.
  + lia.
  + exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hw).
- cbn. tauto.
- exact (conj I (conj I I)).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The cut state between the bcmp calls: INV_INTENT with s3 free (low, or 4 before the box call) *)
Definition IB_RL (v : pfv) (pos : Z) (o : nat) (ln : Z) (gi : nat) (vp s3 : Z) : list (Z * Z) :=
  [(18, 0x23); (24, p_c v); (27, pf_SH v pos); (19, s3)] ++ PF_RM v o ln ++
  [(20, seg_spec.rseg_addr (p_c v) gi); (25, vp)].
Definition IB (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) (s3 : Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  (exists LB : list byte, length LB = 64%nat /\ sa_bytes (rdW Wc memc) (pf_F v pos + PF_O_LOW) LB /\
     firstn (S (length (r_low val 0 64))) (seg_spec.zs LB) = r_low val 0 64 ++ [0]) /\
  pf_rg rX (IB_RL v pos o ln gi vp s3).

Lemma b_rg_s3 : forall (rX rX' : bvmap 5 word) v pos o ln gi vp s3 s3',
  (forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q)) ->
  getr rX' (Z_to_bv 5 19) = w64 s3' ->
  pf_rg rX (IB_RL v pos o ln gi vp s3) -> pf_rg rX' (IB_RL v pos o ln gi vp s3').
Proof.
intros rX rX' v pos o ln gi vp s3 s3' HK H19 H.
unfold pf_rg, IB_RL, PF_RM in *. cbn [app] in *.
rewrite !Forall_cons_iff in *. cbn [fst snd] in *.
destruct H as (R18 & R24 & R27 & _ & R21 & R26 & R20 & R25 & _).
rewrite (HK 18), (HK 24), (HK 27), (HK 21), (HK 26), (HK 20), (HK 25) by (unfold acallee_saved; lia).
repeat split; try assumption. apply Forall_nil.
Qed.

(* the cut carried to a state whose registers keep every callee-saved one but s3, and whose reader is kept
   off the bcmp window *)
Lemma ib_reseat : forall n v pos lyc Sc Wc rX memc mdc rX' memc' mdc' cf nm o ln d gi vp val s3 s3',
  IB n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q)) ->
  getr rX' (Z_to_bv 5 19) = w64 s3' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  IB n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d gi vp val s3'.
Proof.
intros n v pos lyc Sc Wc rX memc mdc rX' memc' mdc' cf nm o ln d gi vp val s3 s3' HIB HJ' HK H19 HM.
destruct HIB as (HB & HMID & HST & HVAL & HINB & (LB & HL64 & HLB & HLZ) & HRG).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI6.
assert (HFI6' : pf_rg rX' (a5_FI B v)) by (apply (b_rg_keep rX rX'); [exact HK | b_forall | exact HFI6]).
split; [exact (b_base_keep B v pos lyc Sc Wc rX memc mdc rX' memc' mdc' PF_SC_LOW HB HJ' HFI6' HM)|].
split; [exact HMID|].
split; [exact (b_st_keep B v pos lyc Sc Wc rX memc mdc memc' PF_SC_LOW _ _ _ _ HB HM HST)|].
split; [exact (b_val_keep B v pos lyc Sc Wc rX memc mdc memc' PF_SC_LOW vp val HB HM HINB HVAL)|].
split; [exact HINB|].
split; [exists LB; split; [exact HL64|]; split; [exact (b_low_keep B v pos lyc Sc Wc rX memc mdc memc' PF_SC_LOW LB HB HM HL64 HLB) | exact HLZ]|].
exact (b_rg_s3 rX rX' v pos o ln gi vp s3 s3' HK H19 HRG).
Qed.

Lemma ib_s3 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3,
  IB n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 -> getr rX (Z_to_bv 5 19) = w64 s3.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 HIB.
destruct HIB as (_ & _ & _ & _ & _ & _ & HRG).
exact (a5_rg_get rX _ 19 s3 HRG ltac:(unfold IB_RL; do 3 right; left; reflexivity)).
Qed.

(* INV_INTENT is IB with s3 = low; INV_ROLEV is IB with s3 = r and r decided *)
Lemma ib_of_intent : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_INTENT B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  IB n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_F v pos + PF_O_LOW).
Proof. intros. exact H. Qed.
Lemma ib_rolev : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r,
  IB n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r ->
  role_intent_parse (r_low val 0 64) = Some r ->
  INV_ROLEV B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r (HB & HMID & HST & _ & _ & _ & HRG) Hr.
split; [exact HB|]. split; [exact HMID|]. split; [exact HST|]. split; [exact Hr|].
split; [exact (a10b_role_range _ _ Hr)|]. exact HRG.
Qed.

(* the seed at a pc of this piece, from pf_base *)
Lemma b_seed_base : forall v pos lyc Sc Wc rX memc mdc sc pc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  st_ok_pi SEGS VAL (b_E rX (pf_F v pos + PF_O_CN)) (b_ss pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc pc HB.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI6.
pose proof HB as (_ & _ & _ & HSL & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
apply (b_seed Wc rX memc pc (pf_s1 v)).
- exact (a5_rg_get rX _ 9 (pf_s1 v) HFI6 ltac:(unfold a5_FI; do 4 right; left; reflexivity)).
- lia.
- lia.
- unfold PF_O_CN. lia.
- exact (proj1 (Forall_forall _ _) HSL (0x50, pf_F v pos + PF_O_CN)
    ltac:(unfold PF_SL; do 6 right; left; reflexivity)).
Qed.

(** ** The bcmp step *)
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).

Lemma ib_call : forall n v pos lyc Sc Wc regsT memT mdT regs2 mem2 md2 cf nm o ln d gi vp val s3,
  IB n v pos lyc Sc Wc regsT memT mdT cf nm o ln d gi vp val s3 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem2 md2 0 ->
  aregs_preserved regsT regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memT a) ->
  IB n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val s3.
Proof.
intros n v pos lyc Sc Wc regsT memT mdT regs2 mem2 md2 cf nm o ln d gi vp val s3 HIB HJ HP HM.
apply (ib_reseat n v pos lyc Sc Wc regsT memT mdT regs2 mem2 md2 cf nm o ln d gi vp val s3 s3 HIB HJ
  (b_pres_keep regsT regs2 HP)); [|exact HM].
rewrite (HP 19 ltac:(unfold acallee_saved; lia)). exact (ib_s3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB).
Qed.

Lemma b_bcmp_step : forall n v pos lyc Sc Wc regsT memT mdT cf nm o ln d gi vp val s3 (w : list Z) (retk : Z) Q,
  IB n v pos lyc Sc Wc regsT memT mdT cf nm o ln d gi vp val s3 ->
  In w m_file_c.MF_ROLE_WORDS ->
  getr regsT 10 = w64 (pf_F v pos + PF_O_LOW) -> getr regsT 11 = w64 (seg_litA_rc w) ->
  getr regsT 12 = w64 (Z.of_nat (S (length w))) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  (forall regs2 mem2 md2,
     IB n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val s3 ->
     (getr regs2 10 = w64 0 <-> strcmp (r_low val 0 64) w = 0) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + retk) regs2 mem2 md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros n v pos lyc Sc Wc regsT memT mdT cf nm o ln d gi vp val s3 w retk Q HIB Hw R10 R11 R12 R1 Hrk Hrk2 K.
pose proof HIB as (HB & HMID & HST & HVAL & HINB & (LB & HL64 & HLB & HLZ) & HRG).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI6.
pose proof HB as (_ & (HJ & _) & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
assert (Hsp : spZ regsT = pf_s1 v).
{ unfold spZ. pose proof (a5_rg_get regsT _ 2 (pf_s1 v) HFI6 ltac:(unfold a5_FI; left; reflexivity)) as H2.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in H2 by (apply bv_eq; reflexivity).
  rewrite H2. unfold w64. apply unsigned_lit_small. lia. }
assert (Hgp : getr regsT 3 = w64 (as_gp B)).
{ pose proof (a5_rg_get regsT _ 3 (as_gp B) HFI6 ltac:(unfold a5_FI; right; left; reflexivity)) as H3.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in H3 by (apply bv_eq; reflexivity). exact H3. }
assert (Htp : getr regsT 4 = w64 (as_tp B)).
{ pose proof (a5_rg_get regsT _ 4 (as_tp B) HFI6 ltac:(unfold a5_FI; right; right; left; reflexivity)) as H4.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in H4 by (apply bv_eq; reflexivity). exact H4. }
pose proof (b_words_len w Hw) as Hwl.
destruct (b_bcmp_pre B v pos lyc Sc Wc regsT memT mdT LB regsT w HB HL64 HLB Hw Hsp)
  as (X0 & X1 & Y0 & Y1 & O16 & Oneg & Obud & SX & SY & WX & WY & MX & MY & RX & HX & RY & HY & LIT).
assert (Ew : pf_sp0 v + (pf_s1 v - pf_sp0 v) = pf_s1 v) by lia.
eapply SRr_bind.
{ apply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIG SS___interceptor_trampoline_bcmp) (ABCMP fx) Wc regsT memT
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v)
    (p_md v) [(5, pos)] lyc Sc mdT 0 (pf_F v pos + PF_O_LOW) (seg_litA_rc w) (Z.of_nat (S (length w)))
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + retk)) HJ R10 R11 R12 ltac:(lia) X0 X1 Y0 Y1
    ltac:(rewrite Hsp; lia) O16 Oneg ltac:(rewrite SPF; rewrite SPF in Obud; exact Obud) Hgp Htp R1
    (ret_ok_codeptr_v retk Hrk Hrk2) SX SY);
    [ rewrite Ew; exact WX | rewrite Ew; exact WY | exact MX | exact MY | exact RX | exact HX | exact RY | exact HY ]. }
intros W' c' _ (-> & regs2 & mem2 & md2 & vr & -> & HJ2 & HP2 & Hres & Hcmp & Hkeep & _).
apply (K regs2 mem2 md2).
- apply (ib_call n v pos lyc Sc Wc regsT memT mdT regs2 mem2 md2 cf nm o ln d gi vp val s3 HIB HJ2 HP2).
  intros a Ha Hn. apply Hkeep; [exact Ha|]. rewrite Ew. exact Hn.
- rewrite Hres, Hcmp.
  exact (a10b_cmp_lit (rdW Wc memT) (pf_F v pos + PF_O_LOW) (seg_litA_rc w) LB (r_low val 0 64) w HL64 HLB HLZ
    (a10b_low_nulfree val 0 64) LIT (a10b_words_nulfree w Hw)).
Qed.

End e.
End f.
End d.

(** ** After the refuse call: JOIN by one `j` (0x884ec), at the FP state refuse returned (a closed section, so
    the walk applies it at that state) *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

Lemma b_rg_join : forall (rX : bvmap 5 word) v pos o ln gi vp s3,
  pf_rg rX (IB_RL v pos o ln gi vp s3) ->
  pf_rg rX ([(18, 0x23); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln ++ [(20, seg_spec.rseg_addr (p_c v) gi)]).
Proof.
intros rX v pos o ln gi vp s3 H. unfold pf_rg, IB_RL, PF_RM in *. cbn [app] in *.
rewrite !Forall_cons_iff in *. tauto.
Qed.

Lemma join_reseat : forall n v pos lyc Sc Wc rX memc mdc rX' mdc' cfx nm o ln d gi,
  INV_JOIN B n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  (forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q)) ->
  INV_JOIN B n v pos lyc Sc Wc rX' memc mdc' cfx nm o ln d gi.
Proof.
intros n v pos lyc Sc Wc rX memc mdc rX' mdc' cfx nm o ln d gi (HB & HMID & HST & HRG) HJ' HK.
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI6.
split.
{ apply (b_base_keep B v pos lyc Sc Wc rX memc mdc rX' memc mdc' PF_SC_LOW HB HJ').
  - apply (b_rg_keep rX rX'); [exact HK | b_forall | exact HFI6].
  - intros a _ _. reflexivity. }
split; [exact HMID|]. split; [exact HST|].
apply (b_rg_keep rX rX'); [exact HK | b_forall | exact HRG].
Qed.

Lemma b_after_refuse : forall n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi,
  HA_JOIN B n ->
  INV_JOIN B n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_REFRET) rX memc mdc) (pf_postm B v (cfx, Some gi, nm) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi HJN HINV.
pose proof HINV as (HB & _).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW PF_REFRET HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
unfold cfg_at. change (w64 (BASE + PF_REFRET)) with (Z_to_bv 64 (BASE + PF_REFRET)).
paj_run_to_sh RUNTOP HS HJ PF_JOIN.
- b_awr.
- eapply frame_of_read_only in HF; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX (pf_F v pos + PF_O_CN))
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pmkst HS. rewrite HF. rewrite HF in HJ.
  exact (HJN fx v pos lyc Sc Wc (ms_regs ms) memc _ cfx nm o ln d gi
    (join_reseat n v pos lyc Sc Wc rX memc mdc (ms_regs ms) _ cfx nm o ln d gi HINV HJ
      (b_kept_keep rX (ms_regs ms) HK))).
Qed.

End e2.
End f2.
End d2.

(** ** The walk: the five bcmp returns and the entry INTENT *)
Section d3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f3.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e3.
Variable B : asyms.
(* the callee texts (pf_pieces.v's list for A10b): the kit's bcmp contract and refuse's contract, at every FP
   state, at the listing's call targets *)
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the abstract instance (SegObj.v): refuse's call target, the literal atoms *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* SSPX and VRO: needed only where the JOIN cut is re-established after the refuse call (pf_a6_k.a6_base_move:
   refuse's journal keeps an image byte only off as_owned_static, and arodata_okP needs pa_relro_img) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis VRO : seg_val_relro (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* the registers of a symbolic state over b_E *)
Lemma b_get_reg : forall (H : word -> bool) rX cn ss ms (r : bv 5) (k : nat),
  st_ok SEGS (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff k 0 -> (k < 32)%nat ->
  getr (ms_regs ms) r = getr rX (Z_to_bv 5 (Z.of_nat k)).
Proof.
intros H rX cn ss ms r k HS Hr Hk. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr.
apply b_den_reg. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia.
Qed.
Lemma b_get_reg_pi : forall (H : word -> bool) rX cn ss ms (r : bv 5) (k : nat),
  st_ok_pi SEGS VAL (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff k 0 -> (k < 32)%nat ->
  getr (ms_regs ms) r = getr rX (Z_to_bv 5 (Z.of_nat k)).
Proof.
intros H rX cn ss ms r k HS Hr Hk. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr.
apply b_den_reg. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia.
Qed.
Lemma b_get_lit_pi : forall (H : word -> bool) rX cn ss ms (r : bv 5) z,
  st_ok_pi SEGS VAL (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z ->
  getr (ms_regs ms) r = w64 z.
Proof. intros H rX cn ss ms r z HS Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr. reflexivity. Qed.
Lemma b_get_lit : forall (H : word -> bool) rX cn ss ms (r : bv 5) z,
  st_ok SEGS (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z ->
  getr (ms_regs ms) r = w64 z.
Proof. intros H rX cn ss ms r z HS Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr. reflexivity. Qed.
Lemma b_get_obj : forall (H : word -> bool) rX cn ss ms (r : bv 5) (i : nat) w,
  st_ok SEGS (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff (A_OBJ i) 0 ->
  (A_OBJ i < A_LIM)%nat -> (i < length seg_objs)%nat -> nth i seg_objs 0 = seg_litA_rc w ->
  getr (ms_regs ms) r = w64 (seg_litA_rc w).
Proof.
intros H rX cn ss ms r i w HS Hr Hi Hl Hn. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr.
cbn [sv_denot]. rewrite (b_E_img rX cn (A_OBJ i)) by (unfold A_OBJ, A_TEXT in *; lia).
rewrite (OBJ i Hl), Z.add_0_r, Hn. reflexivity.
Qed.
Lemma b_get_code : forall (H : word -> bool) rX cn ss ms (r : bv 5) k,
  st_ok SEGS (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff A_TEXT k ->
  getr (ms_regs ms) r = Z_to_bv 64 (BASE + k).
Proof.
intros H rX cn ss ms r k HS Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr.
exact (codeptr_val _ k (b_E_img rX cn)).
Qed.
Lemma b_get_cn : forall (H : word -> bool) rX cn ss ms (r : bv 5),
  st_ok SEGS (b_E rX cn) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff 32 0 ->
  getr (ms_regs ms) r = w64 cn.
Proof.
intros H rX cn ss ms r HS Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. unfold b_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra rX _ 0).
Qed.

(* the four registers of pf_fi a call reads *)
Lemma b_fi_facts : forall v pos lyc Sc Wc rX memc mdc sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  spZ rX = pf_s1 v /\ getr rX 3 = w64 (as_gp B) /\ getr rX 4 = w64 (as_tp B) /\ getr rX 8 = w64 (pf_sp0 v).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc HB.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI6.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof (a5_rg_get rX _ 2 (pf_s1 v) HFI6 ltac:(unfold a5_FI; left; reflexivity)) as H2.
pose proof (a5_rg_get rX _ 3 (as_gp B) HFI6 ltac:(unfold a5_FI; right; left; reflexivity)) as H3.
pose proof (a5_rg_get rX _ 4 (as_tp B) HFI6 ltac:(unfold a5_FI; do 2 right; left; reflexivity)) as H4.
pose proof (a5_rg_get rX _ 8 (pf_sp0 v) HFI6 ltac:(unfold a5_FI; do 3 right; left; reflexivity)) as H8.
replace (Z_to_bv 5 2) with (2%bv : bv 5) in H2 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 3) with (3%bv : bv 5) in H3 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 4) with (4%bv : bv 5) in H4 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 8) with (8%bv : bv 5) in H8 by (apply bv_eq; reflexivity).
split; [unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia|].
split; [exact H3|]. split; [exact H4 | exact H8].
Qed.

(* a value register of the cut *)
Lemma ib_reg : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 r x,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 -> In (r, x) (IB_RL v pos o ln gi vp s3) ->
  getr rX (Z_to_bv 5 r) = w64 x.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 r x (_ & _ & _ & _ & _ & _ & HRG) Hin.
exact (a5_rg_get rX _ r x HRG Hin).
Qed.

Section n.
Variable n : nat.
Hypothesis HJN : HA_JOIN B n.
Hypothesis HRL : HA_ROLEV B n.

(* arriving at ROLEV after a run that wrote nothing, with s3 = r *)
Lemma b_at_rolev : forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 rX' mdc' r,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc' 0 ->
  (forall q, acallee_saved q -> q <> 19 -> getr rX' (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q)) ->
  getr rX' (Z_to_bv 5 19) = w64 r ->
  role_intent_parse (r_low val 0 64) = Some r ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_ROLEV) rX' memc mdc') (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val s3 rX' mdc' r HIB HJ HK H19 Hr.
apply (HRL fx v pos lyc Sc Wc rX' memc mdc' cf nm o ln d gi vp val r). apply ib_rolev; [|exact Hr].
apply (ib_reseat B n v pos lyc Sc Wc rX memc mdc rX' memc mdc' cf nm o ln d gi vp val s3 r HIB HJ HK H19).
intros a _ _. reflexivity.
Qed.

(* 0x884cc, after the box call (s3 = 4): `beqz a0` to ROLEV, else the refuse call and JOIN *)
Lemma ret4_ok : forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val 4 ->
  (forall i wi, (i < 4)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp (r_low val 0 64) wi <> 0) ->
  (getr rX 10 = w64 0 <-> strcmp (r_low val 0 64) S_box = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B_RET4) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HIB HNE HIFF.
pose proof HIB as (HB & HMID & HST & HVAL & HINB & HLOW & HRG).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW B_RET4 HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
pose proof (ib_s3 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB) as H19.
unfold cfg_at. change (w64 (BASE + B_RET4)) with (Z_to_bv 64 (BASE + B_RET4)).
psrr_branch_pi RUNP BR HS.
- (* taken: the word is "box", s3 = 4 already *)
  pose proof (proj1 HIFF (proj2 (b_beqz rX _ true Hc) eq_refl)) as Heq.
  pose proof (a10b_role_some _ 4 S_box eq_refl HNE Heq) as Hr.
  paj_run_to_sh RUNTOP HS HJ PF_ROLEV.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_reg_pi _ _ _ _ _ (Z_to_bv 5 19) 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R19.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    exact (b_at_rolev v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val 4 (ms_regs ms) _ (Z.of_nat 4) HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) (eq_trans R19 H19) Hr).
- (* not taken: none of the five words; refuse(c, ln + 1, F_badrole, cur_name, val), then JOIN *)
  assert (Hne : strcmp (r_low val 0 64) S_box <> 0).
  { intros E0. pose proof (proj1 (b_beqz rX _ false Hc) (proj2 HIFF E0)). discriminate. }
  assert (HNONE : role_intent_parse (r_low val 0 64) = None).
  { apply a10b_role_none. intros w' Hw'. unfold m_file_c.MF_ROLE_WORDS in Hw'.
    destruct Hw' as [<- | [<- | [<- | [<- | [<- | []]]]]].
    - exact (HNE 0%nat S_auto ltac:(lia) eq_refl).
    - exact (HNE 1%nat S_master ltac:(lia) eq_refl).
    - exact (HNE 2%nat S_slave ltac:(lia) eq_refl).
    - exact (HNE 3%nat S_tap ltac:(lia) eq_refl).
    - exact Hne. }
  rewrite (a10b_step_none cf gi nm (ln + 1) val HNONE).
  paj_run_shc RUNP RUNC HS HJ.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_reg _ _ _ _ _ (Z_to_bv 5 19) 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R19.
    pose proof (b_get_reg _ _ _ _ _ 10 24 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R10.
    pose proof (b_get_reg _ _ _ _ _ 11 26 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R11.
    pose proof (b_get_obj _ _ _ _ _ 12 60 F_badrole HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as R12.
    pose proof (b_get_cn _ _ _ _ _ 13 HS ltac:(vm_compute; reflexivity)) as R13.
    pose proof (b_get_reg _ _ _ _ _ 14 25 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R14.
    pose proof (b_get_code _ _ _ _ _ 1 PF_REFRET HS ltac:(vm_compute; reflexivity)) as R1.
    pose proof (eq_trans R10 (ib_reg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 24 (p_c v) HIB
      ltac:(unfold IB_RL; right; left; reflexivity))) as R10'. clear R10. rename R10' into R10.
    pose proof (eq_trans R11 (ib_reg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 26 (ln + 1) HIB
      ltac:(unfold IB_RL, PF_RM; do 5 right; left; reflexivity))) as R11'. clear R11. rename R11' into R11.
    pose proof (eq_trans R14 (ib_reg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 25 vp HIB
      ltac:(unfold IB_RL, PF_RM; do 7 right; left; reflexivity))) as R14'. clear R14. rename R14' into R14.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    (* the cut at the call state *)
    pose proof (ib_reseat B n v pos lyc Sc Wc rX memc mdc (ms_regs ms) memc _ cf nm o ln d gi vp val 4 4 HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) (eq_trans R19 H19) ltac:(intros; reflexivity)) as HIB'.
    pose proof HIB' as (HB' & _ & HST' & HVAL' & _ & _ & HRG').
    destruct (b_fi_facts v pos lyc Sc Wc (ms_regs ms) memc _ PF_SC_LOW HB') as (Hsp & Hgp & Htp & R8).
    pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & G & _).
    pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
    pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & _). rewrite <- a6_s1_eq in S1a.
    pose proof STK_values as (_ & SREF & _ & SPF & _).
    pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
    assert (EREF : PF_REFRET = 14264) by reflexivity.
    assert (Ew : pf_sp0 v + (pf_s1 v - pf_sp0 v) = pf_s1 v) by lia.
    destruct (b_refuse_pre B n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val (ms_regs ms) HB' HMID HST'
      HVAL' HINB R10 R11 R12 R13 R14 Hsp R8)
      as ((ch1 & Hch) & Hroom & Hev & Hc64 & Hl64 & Hfp64 & HRP & HFPin).
    pose proof HB' as (_ & (HJ' & _) & HOBJ' & _).
    pose proof HOBJ' as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
    rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
    replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
    destruct (b_o_bounds (pf_sp0 v) (pf_s1 v) G3 G5 S1a) as (Omod & Olo).
    eapply SRr_bind.
    { eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
        (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0
        STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_REFRET)) ch1
        (fun ly2 S2 W2 regs2 mem2 md2 =>
           sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badrole [AS nm; AS val]) /\
           sa_noalloc B lyc Sc ly2 S2) HJ').
      - rewrite Hsp. lia.
      - exact Omod.
      - lia.
      - rewrite SREF. lia.
      - rewrite SREF, SPF. lia.
      - exact Hgp.
      - exact Htp.
      - exact R1.
      - apply ret_ok_codeptr_v; [rewrite EREF; lia | rewrite EREF; reflexivity].
      - rewrite EREF. rewrite unsigned_lit_small by lia. lia.
      - rewrite Ew. exact Hch.
      - intros HPRE1. eapply SRr_mono.
        { apply (REFUSE fx lyc Sc Wc (ms_regs ms) memc _ ch1 (p_c v) (ln + 1) (seg_litA_rc F_badrole) (ln + 1) cf
            F_badrole [AS nm; AS val] HPRE1 HROD R10 Hc64 R11 Hl64 R12 Hfp64 HRP Hroom Hev). }
        cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJx & HPx & HKx).
        exists fx', ly', S', regs', mem', md'. split; [rewrite R1; reflexivity|].
        split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJx|]. split; [exact HPx | exact HKx].
      - exact HFPin. }
    cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
    rewrite Ew in HJc2.
    pose proof (b_join B SSPX VRO fx1 n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val (ms_regs ms)
      ly2 S2 W2 regs2 mem2 md2 Hfx1 HB' HMID HST' HVAL' HINB Hsp
      (b_rg_join (ms_regs ms) v pos o ln gi vp 4 HRG') (a5_fi_regs B _ _ _ _ _ _ _ _ _ HB')
      HJ2 HJc2 HP2 HRC2 HNA2) as HINVJ.
    unfold pf_postm, PF_POSTr.
    eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
    exact (b_after_refuse (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 _ nm o ln d gi HJN HINVJ).
Qed.

(* one more word compared and different: the "not equal" facts of the next return *)
Lemma b_ne_step : forall (l : list Z) (j : nat) (w : list Z),
  nth_error m_file_c.MF_ROLE_WORDS j = Some w -> strcmp l w <> 0 ->
  (forall i wi, (i < j)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp l wi <> 0) ->
  forall i wi, (i < S j)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp l wi <> 0.
Proof.
intros l j w Hj Hne HNE i wi Hi Hwi. destruct (Nat.eq_dec i j) as [-> | Hij].
- rewrite Hj in Hwi. injection Hwi as <-. exact Hne.
- exact (HNE i wi ltac:(lia) Hwi).
Qed.

(* 0x884ac, after the tap call: `beqz a0` to 0x8883c (s3 = 3, falls into ROLEV), else the box call *)
Lemma ret3_ok : forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_F v pos + PF_O_LOW) ->
  (forall i wi, (i < 3)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp (r_low val 0 64) wi <> 0) ->
  (getr rX 10 = w64 0 <-> strcmp (r_low val 0 64) S_tap = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B_RET3) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HIB HNE HIFF.
pose proof HIB as (HB & _).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW B_RET3 HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
pose proof (ib_s3 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB) as H19.
unfold cfg_at. change (w64 (BASE + B_RET3)) with (Z_to_bv 64 (BASE + B_RET3)).
psrr_branch_pi RUNP BR HS.
- pose proof (proj1 HIFF (proj2 (b_beqz rX _ true Hc) eq_refl)) as Heq.
  pose proof (a10b_role_some _ 3 S_tap eq_refl HNE Heq) as Hr.
  paj_run_to_sh RUNTOP HS HJ PF_ROLEV.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_lit_pi _ _ _ _ _ (Z_to_bv 5 19) 3 HS ltac:(vm_compute; reflexivity)) as R19.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    exact (b_at_rolev v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ (ms_regs ms) _ (Z.of_nat 3) HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 Hr).
- assert (Hne : strcmp (r_low val 0 64) S_tap <> 0).
  { intros E0. pose proof (proj1 (b_beqz rX _ false Hc) (proj2 HIFF E0)). discriminate. }
  paj_run_shc RUNP RUNC HS HJ.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_lit _ _ _ _ _ (Z_to_bv 5 19) 4 HS ltac:(vm_compute; reflexivity)) as R19.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ 10 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19) as R10.
    pose proof (b_get_obj _ _ _ _ _ 11 59 S_box HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as R11.
    pose proof (b_get_lit _ _ _ _ _ 12 (Z.of_nat (S (length S_box))) HS ltac:(vm_compute; reflexivity)) as R12.
    pose proof (b_get_code _ _ _ _ _ 1 B_RET4 HS ltac:(vm_compute; reflexivity)) as R1.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    pose proof (ib_reseat B n v pos lyc Sc Wc rX memc mdc (ms_regs ms) memc _ cf nm o ln d gi vp val _ 4 HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 ltac:(intros; reflexivity)) as HIB'.
    apply (b_bcmp_step B ABCMP n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val 4 S_box B_RET4 _ HIB'
      ltac:(unfold m_file_c.MF_ROLE_WORDS; do 4 right; left; reflexivity) R10 R11 R12 R1
      ltac:(rewrite (eq_refl : B_RET4 = 14232); lia) eq_refl).
    intros regs2 mem2 md2 HIB2 HIFF2.
    exact (ret4_ok v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val HIB2
      (b_ne_step _ 3 S_tap eq_refl Hne HNE) HIFF2).
Qed.

(* 0x88494, after the slave call: `beqz a0` to 0x8879c (s3 = 2), else the tap call *)
Lemma ret2_ok : forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_F v pos + PF_O_LOW) ->
  (forall i wi, (i < 2)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp (r_low val 0 64) wi <> 0) ->
  (getr rX 10 = w64 0 <-> strcmp (r_low val 0 64) S_slave = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B_RET2) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HIB HNE HIFF.
pose proof HIB as (HB & _).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW B_RET2 HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
pose proof (ib_s3 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB) as H19.
unfold cfg_at. change (w64 (BASE + B_RET2)) with (Z_to_bv 64 (BASE + B_RET2)).
psrr_branch_pi RUNP BR HS.
- pose proof (proj1 HIFF (proj2 (b_beqz rX _ true Hc) eq_refl)) as Heq.
  pose proof (a10b_role_some _ 2 S_slave eq_refl HNE Heq) as Hr.
  paj_run_to_sh RUNTOP HS HJ PF_ROLEV.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_lit_pi _ _ _ _ _ (Z_to_bv 5 19) 2 HS ltac:(vm_compute; reflexivity)) as R19.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    exact (b_at_rolev v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ (ms_regs ms) _ (Z.of_nat 2) HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 Hr).
- assert (Hne : strcmp (r_low val 0 64) S_slave <> 0).
  { intros E0. pose proof (proj1 (b_beqz rX _ false Hc) (proj2 HIFF E0)). discriminate. }
  paj_run_shc RUNP RUNC HS HJ.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ (Z_to_bv 5 19) 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19)
      as R19.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ 10 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19) as R10.
    pose proof (b_get_obj _ _ _ _ _ 11 58 S_tap HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as R11.
    pose proof (b_get_lit _ _ _ _ _ 12 (Z.of_nat (S (length S_tap))) HS ltac:(vm_compute; reflexivity)) as R12.
    pose proof (b_get_code _ _ _ _ _ 1 B_RET3 HS ltac:(vm_compute; reflexivity)) as R1.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    pose proof (ib_reseat B n v pos lyc Sc Wc rX memc mdc (ms_regs ms) memc _ cf nm o ln d gi vp val _ _ HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 ltac:(intros; reflexivity)) as HIB'.
    apply (b_bcmp_step B ABCMP n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val _ S_tap B_RET3 _ HIB'
      ltac:(unfold m_file_c.MF_ROLE_WORDS; repeat (first [left; reflexivity | right])) R10 R11 R12 R1
      ltac:(rewrite (eq_refl : B_RET3 = 14200); lia) eq_refl).
    intros regs2 mem2 md2 HIB2 HIFF2.
    exact (ret3_ok v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val HIB2
      (b_ne_step _ 2 S_slave eq_refl Hne HNE) HIFF2).
Qed.

(* 0x8847c, after the master call: `beqz a0` to 0x885a0 (s3 = 1), else the slave call *)
Lemma ret1_ok : forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_F v pos + PF_O_LOW) ->
  (forall i wi, (i < 1)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp (r_low val 0 64) wi <> 0) ->
  (getr rX 10 = w64 0 <-> strcmp (r_low val 0 64) S_master = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B_RET1) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HIB HNE HIFF.
pose proof HIB as (HB & _).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW B_RET1 HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
pose proof (ib_s3 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB) as H19.
unfold cfg_at. change (w64 (BASE + B_RET1)) with (Z_to_bv 64 (BASE + B_RET1)).
psrr_branch_pi RUNP BR HS.
- pose proof (proj1 HIFF (proj2 (b_beqz rX _ true Hc) eq_refl)) as Heq.
  pose proof (a10b_role_some _ 1 S_master eq_refl HNE Heq) as Hr.
  paj_run_to_sh RUNTOP HS HJ PF_ROLEV.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_lit_pi _ _ _ _ _ (Z_to_bv 5 19) 1 HS ltac:(vm_compute; reflexivity)) as R19.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    exact (b_at_rolev v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ (ms_regs ms) _ (Z.of_nat 1) HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 Hr).
- assert (Hne : strcmp (r_low val 0 64) S_master <> 0).
  { intros E0. pose proof (proj1 (b_beqz rX _ false Hc) (proj2 HIFF E0)). discriminate. }
  paj_run_shc RUNP RUNC HS HJ.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ (Z_to_bv 5 19) 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19)
      as R19.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ 10 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19) as R10.
    pose proof (b_get_obj _ _ _ _ _ 11 57 S_slave HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as R11.
    pose proof (b_get_lit _ _ _ _ _ 12 (Z.of_nat (S (length S_slave))) HS ltac:(vm_compute; reflexivity)) as R12.
    pose proof (b_get_code _ _ _ _ _ 1 B_RET2 HS ltac:(vm_compute; reflexivity)) as R1.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    pose proof (ib_reseat B n v pos lyc Sc Wc rX memc mdc (ms_regs ms) memc _ cf nm o ln d gi vp val _ _ HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 ltac:(intros; reflexivity)) as HIB'.
    apply (b_bcmp_step B ABCMP n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val _ S_slave B_RET2 _ HIB'
      ltac:(unfold m_file_c.MF_ROLE_WORDS; repeat (first [left; reflexivity | right])) R10 R11 R12 R1
      ltac:(rewrite (eq_refl : B_RET2 = 14176); lia) eq_refl).
    intros regs2 mem2 md2 HIB2 HIFF2.
    exact (ret2_ok v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val HIB2
      (b_ne_step _ 1 S_master eq_refl Hne HNE) HIFF2).
Qed.

(* 0x88464, after the auto call: `beqz a0` to 0x884f0 (s3 = 0), else the master call *)
Lemma ret0_ok : forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  IB B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_F v pos + PF_O_LOW) ->
  (forall i wi, (i < 0)%nat -> nth_error m_file_c.MF_ROLE_WORDS i = Some wi -> strcmp (r_low val 0 64) wi <> 0) ->
  (getr rX 10 = w64 0 <-> strcmp (r_low val 0 64) S_auto = 0) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B_RET0) rX memc mdc) (pf_postm B v (pf_role_step cf gi nm (ln + 1) val) o ln).
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HIB HNE HIFF.
pose proof HIB as (HB & _).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW B_RET0 HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
pose proof (ib_s3 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB) as H19.
unfold cfg_at. change (w64 (BASE + B_RET0)) with (Z_to_bv 64 (BASE + B_RET0)).
psrr_branch_pi RUNP BR HS.
- pose proof (proj1 HIFF (proj2 (b_beqz rX _ true Hc) eq_refl)) as Heq.
  pose proof (a10b_role_some _ 0 S_auto eq_refl HNE Heq) as Hr.
  paj_run_to_sh RUNTOP HS HJ PF_ROLEV.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity]. cbn [ms_mem mkst] in HF.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (b_get_lit_pi _ _ _ _ _ (Z_to_bv 5 19) 0 HS ltac:(vm_compute; reflexivity)) as R19.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    exact (b_at_rolev v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val _ (ms_regs ms) _ (Z.of_nat 0) HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 Hr).
- assert (Hne : strcmp (r_low val 0 64) S_auto <> 0).
  { intros E0. pose proof (proj1 (b_beqz rX _ false Hc) (proj2 HIFF E0)). discriminate. }
  paj_run_shc RUNP RUNC HS HJ.
  + b_awr.
  + eapply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ (Z_to_bv 5 19) 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19)
      as R19.
    pose proof (eq_trans (b_get_reg _ _ _ _ _ 10 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19) as R10.
    pose proof (b_get_obj _ _ _ _ _ 11 56 S_master HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as R11.
    pose proof (b_get_lit _ _ _ _ _ 12 (Z.of_nat (S (length S_master))) HS ltac:(vm_compute; reflexivity)) as R12.
    pose proof (b_get_code _ _ _ _ _ 1 B_RET1 HS ltac:(vm_compute; reflexivity)) as R1.
    pmkst HS. rewrite HF. rewrite HF in HJ.
    pose proof (ib_reseat B n v pos lyc Sc Wc rX memc mdc (ms_regs ms) memc _ cf nm o ln d gi vp val _ _ HIB HJ
      (b_kept_keep rX (ms_regs ms) HK) R19 ltac:(intros; reflexivity)) as HIB'.
    apply (b_bcmp_step B ABCMP n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val _ S_master B_RET1 _ HIB'
      ltac:(unfold m_file_c.MF_ROLE_WORDS; repeat (first [left; reflexivity | right])) R10 R11 R12 R1
      ltac:(rewrite (eq_refl : B_RET1 = 14152); lia) eq_refl).
    intros regs2 mem2 md2 HIB2 HIFF2.
    exact (ret1_ok v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val HIB2
      (b_ne_step _ 0 S_auto eq_refl Hne HNE) HIFF2).
Qed.

(* INTENT 0x88450: the auto call *)
Lemma intent_ok : H_INTENT B n.
Proof.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HINV.
pose proof (ib_of_intent B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HINV) as HIB.
pose proof HIB as (HB & _).
pose proof (b_seed_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW PF_INTENT HB) as HS.
pose proof HB as (_ & (HJ & _) & _).
pose proof (b_E_img (PI := PI) rX (pf_F v pos + PF_O_CN)) as HEI.
pose proof (ib_s3 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HIB) as H19.
unfold cfg_at. change (w64 (BASE + PF_INTENT)) with (Z_to_bv 64 (BASE + PF_INTENT)).
paj_run_shc RUNP RUNC HS HJ.
- b_awr.
- eapply frame_of_read_only in HF; [|vm_compute; reflexivity].
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) B_CS) HS (b_E_agree rX _)
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (eq_trans (b_get_reg _ _ _ _ _ (Z_to_bv 5 19) 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19)
    as R19.
  pose proof (eq_trans (b_get_reg _ _ _ _ _ 10 19 HS ltac:(vm_compute; reflexivity) ltac:(lia)) H19) as R10.
  pose proof (b_get_obj _ _ _ _ _ 11 55 S_auto HS ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as R11.
  pose proof (b_get_lit _ _ _ _ _ 12 (Z.of_nat (S (length S_auto))) HS ltac:(vm_compute; reflexivity)) as R12.
  pose proof (b_get_code _ _ _ _ _ 1 B_RET0 HS ltac:(vm_compute; reflexivity)) as R1.
  pmkst HS. rewrite HF. rewrite HF in HJ.
  pose proof (ib_reseat B n v pos lyc Sc Wc rX memc mdc (ms_regs ms) memc _ cf nm o ln d gi vp val _ _ HIB HJ
    (b_kept_keep rX (ms_regs ms) HK) R19 ltac:(intros; reflexivity)) as HIB'.
  apply (b_bcmp_step B ABCMP n v pos lyc Sc Wc (ms_regs ms) memc _ cf nm o ln d gi vp val _ S_auto B_RET0 _ HIB'
    ltac:(unfold m_file_c.MF_ROLE_WORDS; left; reflexivity) R10 R11 R12 R1
    ltac:(unfold B_RET0, AF_reac_segconf_parse_file; lia) eq_refl).
  intros regs2 mem2 md2 HIB2 HIFF2.
  exact (ret0_ok v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d gi vp val HIB2
    (fun i wi Hi _ => False_ind _ (Nat.nlt_0_r i Hi)) HIFF2).
Qed.

End n.
End e3.
End f3.
End d3.

(** ** The piece: HA_JOIN n -> HA_ROLEV n -> H_INTENT n at every ambient FP state *)
Section g. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_bcmp).
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* SSPX and VRO: forced only by pf_a6_k.a6_base_move after the refuse call (pf_a10b_b4.b_join) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis VRO : seg_val_relro (PI := PI).
Theorem pa10_b_ok : PA10_B B.
Proof.
intros f0 n HJN HRL.
exact (intent_ok (fx := f0) B ABCMP REFUSE SIGP OBJ SSPX VRO n HJN HRL).
Qed.
End g.
