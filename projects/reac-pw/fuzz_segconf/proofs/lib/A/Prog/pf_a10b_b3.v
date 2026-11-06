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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 130 of its 162 lines of code are new or changed and 421 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment piece PA10_B of reac_segconf_parse_file's walk, the
   premises of the call of refuse at 0x884e8 (refuse(c, ln + 1, F_badrole, cur_name, val)): part of segment A10b's
   proof, by the G3 walk owner, 2026-10-30. No instruction is walked here.
   b_refuse_pre (P4, statement fixed by the A10b proof's B-interface file; working notes, not in the tree): at the call, every
   premise PaFx.cl_callSF and refuse_contract ask beyond the registers: the frame chain (pf_a5_k.a5_chain), the
   room for refuse's class-0 frame, the event bound, the argument ranges, refuse_pre, and refuse's footprint inside
   parse_file's.
   The two %s arguments lie in parse_file's own class-5 frame, both in scope at PF_SC_LOW, and both go through
   pf_a6_k.a6_obj_arg: cur_name at [F + 0x20, F + 0x30) (shadow cells 4..5; b3_nm_str turns pf_nm into its C
   string) and val in buf (pf_a6_k.a6_buf_arg, a6_obj_arg's instance at [F + 0x40, F + 0x240), cells 8..71).
   No Section hypothesis: sa_ssp is pf_obj's last conjunct at the call site, and nothing here needs the read-only
   range, so the interface's SSPX and VRO are dropped. *)
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
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegGlob SegInstA SegObj refuse_c reac_segconf_parse_file_c pf_pieces pf_a10b_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_k pf_a6_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the first k bytes of a list agree with the list below k *)
Lemma b3_nth_firstn : forall (l : list Z) (k i : nat), (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
induction l as [|x l IH]; intros k i Hi; destruct k as [|k]; try lia.
- destruct i; reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
(* cur_name's 16 bytes hold the C string nm (pf_nm): it is a C string with its slack, when cur_name is 8-aligned *)
Lemma b3_nm_str : forall (rd : reader) (a : Z) (nm : list Z), pf_nm rd a nm -> a mod 8 = 0 ->
  sa_str rd a nm /\ (length nm < 16)%nat.
Proof.
intros rd a nm (f & Hb & (Hl & Hlt & Hn0 & Hfz)) Ha8.
split; [|exact Hlt].
assert (Hnth : forall i, (i < S (length nm))%nat -> rd (a + Z.of_nat i) = Some (nth i (nm ++ [0]) 0)).
{ intros i Hi. rewrite (Hb i) by lia. f_equal.
  rewrite <- Hfz, (b3_nth_firstn _ _ _ Hi). unfold seg_spec.zs.
  rewrite <- (map_nth bv_unsigned f ZB0 i).
  apply nth_indep. rewrite length_map. lia. }
split.
- split; [|exact Hn0]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hnth. lia.
- intros y Hy.
  pose proof (Z.div_mod (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod a 8 ltac:(lia)) as D3. rewrite Ha8, Z.add_0_r in D3.
  assert (Hy2 : a < y < a + 16) by lia.
  replace y with (a + Z.of_nat (Z.to_nat (y - a))) by lia.
  rewrite (Hb (Z.to_nat (y - a))) by lia. discriminate.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* ---- P4: the premises of PaFx.cl_callSF and of refuse_contract at the refuse call 0x884e8 ---- *)
Lemma b_refuse_pre : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (regsc : bvmap 5 word),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) ->
  sa_str (rdW Wc memc) vp val -> pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  getr regsc 10 = w64 (p_c v) -> getr regsc 11 = w64 (ln + 1) -> getr regsc 12 = w64 (seg_litA_rc F_badrole) ->
  getr regsc 13 = w64 (pf_F v pos + PF_O_CN) -> getr regsc 14 = w64 vp ->
  spZ regsc = pf_s1 v -> getr regsc 8 = w64 (pf_sp0 v) ->
  (exists ch1, achain lyc (rdW Wc memc) (pf_s1 v) (s0Z regsc) ch1) /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX /\
  0 <= p_c v < 2 ^ 64 /\ 0 <= ln + 1 < 2 ^ 64 /\ 0 <= seg_litA_rc F_badrole < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regsc (rdW Wc memc) (p_c v) (ln + 1)
    (seg_litA_rc F_badrole) [getr regsc 13; getr regsc 14; getr regsc 15; getr regsc 16; getr regsc 17]
    cf (ln + 1) F_badrole [AS nm; AS val] /\
  (forall a, inFP (refuse_W (p_c v) cf) a ->
     (inFP (seg_spec.RC_PARSE_W (p_c v)) a /\
      exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m) \/
     in_tmp_block (ablocks B (p_ly v) (p_S v)) (ablocks B lyc Sc) a).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val regsc HB MID ST Hvs Hvb H10 H11 H12 H13 H14 Hsp H8.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & _).
destruct (a5_chain B _ _ _ _ _ _ _ _ _ HB) as (ch1 & Hch).
pose proof HB as (CX & FI & OBJ & _ & _).
destruct (a6_cx B v CX) as (Hc0 & Hc16 & HLS & _ & Hceil & _ & _ & _).
pose proof CX as (_ & _ & _ & Hc64 & _ & _ & _ & _ & _ & Hroom & Hev).
pose proof FI as (HJ & _ & _ & _ & _ & _ & HFRM & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof OBJ as (_ & _ & _ & AC & HC & _ & LITS & _ & SSP).
pose proof ST as (RC & _ & NM & CNT).
pose proof MID as (_ & _ & LCX).
destruct (pf_lctx_ln _ _ _ _ LCX) as (Hln & Hnx).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
assert (Hl1 : 0 <= ln + 1 <= 65535) by lia.
assert (Hs0 : s0Z regsc = pf_sp0 v) by (unfold s0Z; rewrite H8; apply a6_w64_u; lia).
destruct (a6_heap_bounds B _ _ _ _ _ _ _ HAR HC ltac:(unfold seg_spec.SEG_C_SIZE; lia))
  as (bc & mc & Hinc & Hcb1 & Hcb2 & _).
(* the format: a literal of parse_file's module *)
assert (HLin : In F_badrole PARSE_FILE_LITS).
{ unfold PARSE_FILE_LITS. apply in_or_app. left. do 15 apply in_cons. apply in_eq. }
pose proof (LITS F_badrole HLin) as HLL.
pose proof HLL as (Hlp & _ & Hpin & _).
pose proof (Hpin _ _ _ _ _ HAR) as (_ & Hlhi & _).
(* the forbidden ranges of refuse_pre's sa_va_args: the stack above alloc_ceiling, two ranges in the block c *)
assert (HWl : Forall (fun iv => alloc_ceiling <= fst iv \/
    (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= fst iv /\ snd iv <= b + req_size m))
  [(ly_stk_lo lyc, spZ regsc);
   (seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)),
    seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)) + seg_spec.RC_REFUSAL_LEN);
   (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]).
{ destruct RC as (bs & _ & (_ & _ & _ & _ & HL8 & _)).
  constructor; [left; cbn [fst]; rewrite Hly; exact Hceil|].
  constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.SEG_C_SIZE in *; lia|].
  constructor; [right; exists bc, mc; split; [exact Hinc|]; cbn [fst snd];
    unfold seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *; lia|].
  constructor. }
(* the two %s arguments: cur_name (a3) and val in buf (a4) *)
(* cur_name: pf_nm gives the C string (b3_nm_str); pf_a6_k.a6_obj_arg at [F + 0x20, F + 0x30), cells 4..5 *)
assert (Hcn8 : (pf_F v pos + PF_O_CN) mod 8 = 0).
{ pose proof G as (_ & _ & _ & _ & _ & _ & _ & HF32 & _).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF32. rewrite HF32, Z.add_0_r in DF32.
  unfold PF_O_CN. pose proof (Z.div_mod (pf_F v pos + 32) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (pf_F v pos + 32) 8 ltac:(lia)). lia. }
destruct (b3_nm_str _ _ _ NM Hcn8) as [Hnms Hnml].
assert (Hcell : forall i, 0x20 / 8 <= i < 0x30 / 8 -> pf_shb PF_SC_LOW i = 0).
{ intros i Hi. change (0x20 / 8) with 4 in Hi. change (0x30 / 8) with 6 in Hi. unfold pf_shb.
  destruct (i <? 4) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  destruct (i <? 6) eqn:E2; [reflexivity | apply Z.ltb_ge in E2; lia]. }
destruct (a6_obj_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LOW 0x20 0x30 (pf_F v pos + PF_O_CN) nm _ HB
  ltac:(lia) eq_refl eq_refl ltac:(lia) Hcell Hnms ltac:(unfold PF_O_CN; lia) ltac:(unfold PF_O_CN; lia) HWl)
  as (VN & LN).
destruct (a6_buf_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LOW vp val _ HB eq_refl eq_refl Hvs Hvb HWl) as (VV & LV).
split; [exists ch1; rewrite Hs0; exact Hch|].
split; [unfold sa_room; unfold sa_room_n in Hroom; rewrite Hfrs; cbn [app length]; lia|].
split; [unfold EV_refuse; unfold EV_reac_segconf_parse_file in Hev; lia|].
split; [exact Hc64|].
split; [lia|].
split; [lia|].
split.
- unfold refuse_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [exact HC|]. split; [exact AC|].
  split; [destruct CNT as [CN1 _]; lia|].
  split; [lia|]. split; [reflexivity|].
  split; [unfold seg_spec.REFUSE_FORMATS; do 10 apply in_cons; apply in_eq|].
  split; [cbn [map seg_spec.arg_is_s]; vm_compute; reflexivity|].
  split; [lia|]. split; [reflexivity|]. split; [exact HLL|].
  split; [cbn [sa_va_args]; rewrite H13, H14; exact (conj VN (conj VV I))|].
  split; [cbn [refuse_va_locs]; rewrite H13, H14; exact (conj LN (conj LV I))|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
- intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ _ Ha)|].
  exists bc, mc. split; [exact Hinc|]. apply a6_refuse_W_in_block in Ha.
  unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia.
Qed.

End e.
End f.
End d.
