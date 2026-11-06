(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): piece PB10_S of
   segment B10b of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B10b_k.v: HA_JOIN n -> H_ROLEV n), its second
   half: from the call of snprintf at 0x88dc4 (after the token run of 0x88d6c .. 0x88dc0) to the cut JOIN 0x88dc8.
   A B10b sub-lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: helper lemmas of a segment lemma of
   reac_segconf_parse_file's walk); no instruction is walked here, only the call step.
   Section hypotheses (lib/B/Prog/pf_seg_B10b_s.v names them; the segment's piece list, section 3):
     ASNP  forall fx0, RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf)
           gotwA guardA  (the snprintf wrapper at its trampoline, the stack-protector cells of SegInstB).
   ADAPTED from 501c0d516c69 proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s4.v (an snprintf site: the
   step, srr_after_artF and the continuation at the FP state fx1 the wrapper returns), with the step of
   pf_seg_B10b_sf.v (b10s_aj_snprintf_atSF, the journal form) and the "%s" family instance b10s_FR_s_regs; the JOIN
   cut rebuilt as the B10b segment lane's pf_seg_B10b_j.v rebuilds TAIL (the keep lemmas of pf_seg_B10b_sg.v), and the
   block's new state by pf_seg_B10b_f.v's b10b_rconf_role (the two `sw` and the role_file bytes).
     b10s_join     INV_JOIN at the return state, from INV_ROLEV, what the token run did (the two role words written,
                   every other byte kept) and what snprintf did (c->reading and its NUL at &c->seg[gi].role_file,
                   every other byte outside the destination and the window below s1 kept).
     b10s_from_call  the call 0x88dc4 snprintf(cur + 0xa0, 96, 0x21340 "%s", c + RC_READING) to H_JOIN at fx1. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat RtPFCmd RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k pf_seg_B10b_f
  pf_seg_B10b_sf pf_seg_B10b_sg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- pure facts ---------- *)
(* the hull of a sub-range lies in the hull of the range (trim_s.v tr_hull_sub) *)
Lemma b10s_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 Hn s Hs. apply H.
pose proof (Z.div_le_mono (shadow_addr x) (shadow_addr x') 8 ltac:(lia) (shadow_mono x x' H1)) as D1.
pose proof (Z.div_le_mono (shadow_addr (x' + n' - 1)) (shadow_addr (x + n - 1)) 8 ltac:(lia)
  (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia))) as D2.
lia.
Qed.
Lemma b10s_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 < n' ->
  sa_addr rd q' n'.
Proof.
intros rd q n q' n' (H0 & H1 & H2 & H3 & H4) Hq Hn Hp.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
split; [exact (range_addressable_sub _ _ q n q' n' H3 Hq Hn)|].
intros _. exact (b10s_hull_sub rd q n q' n' (H4 ltac:(lia)) Hq Hn Hp).
Qed.
(* a value of the ASan reader is a byte *)
Lemma b10s_val_range : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof. exact sa_aview_rng. Qed.
(* the n bytes val_mem fixes, as the reader shows them *)
Lemma b10s_sa_val : forall segs H mem a (n : nat) v, val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* snprintf(d, 96, "%s", T) with |T| < 96 writes T and its NUL *)
Lemma b10s_sn_bytes : forall T : list Z, (length T < 96)%nat -> RtPFShared.sn_bytes (96 - 1) T = T ++ [0].
Proof. intros T H. unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity | lia]. Qed.
Lemma b10s_sn_len : forall T : list Z, (length T < 96)%nat -> RtPFShared.sn_len (96 - 1) T = Z.of_nat (length T) + 1.
Proof. intros T H. unfold RtPFShared.sn_len. rewrite b10s_sn_bytes by exact H. rewrite length_app. cbn [length]. lia. Qed.
(* the T30 test `andi a0,a0,3; bnez a0` on cur, a multiple of 4 *)
Lemma b10s_t30 : forall E x, ew E 32 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> x mod 4 = 0 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 3))) (sv_denot E (SLit 0)) = false.
Proof.
intros E x H Hx H4. rewrite branch_ne_U, U_and_lit by lia. rewrite (U_atom E 32 x H Hx), U_lit by lia.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite H4. reflexivity.
Qed.
(* cur = c + 356 gi with c a multiple of 16 is a multiple of 4 *)
Lemma b10s_cur4 : forall c (gi : nat), c mod 16 = 0 -> (seg_spec.rseg_addr c gi) mod 4 = 0.
Proof.
intros c gi H. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE.
apply Z.mod_divide in H as [q Hq]; [|lia]. rewrite Hq.
replace (q * 16 + 356 * Z.of_nat gi) with ((4 * q + 89 * Z.of_nat gi) * 4) by lia. apply Z_mod_mult.
Qed.
(* c->reading as a C string with its slack, from the block's encoding (the field lies 8-aligned in the block) *)
Lemma b10s_reading_str : forall (rd : reader) c cf, sa_rconf rd c cf -> c mod 8 = 0 ->
  sa_str rd (c + seg_spec.RC_READING) (rc_reading cf) /\
  (forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rd x <> None) /\
  (length (rc_reading cf) < 96)%nat /\ ~ In 0 (rc_reading cf).
Proof.
intros rd c cf (bs & HB & HE) H8.
destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (Hl96 & Hlt & Hnz & Hfst).
unfold seg_spec.SEG_C_SIZE in HL.
assert (Hsome : forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rd x <> None).
{ intros x Hx. unfold seg_spec.SEG_C_SIZE in Hx.
  replace x with (c + Z.of_nat (Z.to_nat (x - c))) by lia. rewrite (HB (Z.to_nat (x - c)) ltac:(lia)). discriminate. }
split; [|split; [exact Hsome | split; [exact Hlt | exact Hnz]]].
split; [split; [|exact Hnz]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  assert (Ei : nth i (rc_reading cf ++ [0]) 0 = nth i (seg_spec.zs (seg_spec.fldz seg_spec.RC_READING 96 bs)) 0).
  { rewrite <- Hfst. rewrite nth_firstn. destruct (Nat.ltb_spec i (S (length (rc_reading cf)))); [reflexivity | lia]. }
  rewrite Ei. unfold seg_spec.fldz.
  rewrite b10f_nth_zs by (rewrite b10f_len_fld by (unfold seg_spec.RC_READING; lia); lia).
  rewrite b10f_nth_fld by lia.
  replace (c + seg_spec.RC_READING + Z.of_nat i) with (c + Z.of_nat (Z.to_nat seg_spec.RC_READING + i))
    by (unfold seg_spec.RC_READING; lia).
  apply HB. unfold seg_spec.RC_READING. lia.
- intros x Hx. apply Hsome. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *.
  pose proof (Z.mod_pos_bound (c + 16512 + Z.of_nat (length (rc_reading cf))) 8 ltac:(lia)). lia.
Qed.
(* a C string and its slack carried to a reader that agrees on its bytes and the 8 after its NUL *)
Lemma b10s_str_keep : forall (rd rd' : reader) p s, sa_str rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 8 -> rd' x = rd x) -> sa_str rd' p s.
Proof.
intros rd rd' p s ((Hz & Hn) & Ht) K. split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite K by lia.
  exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). rewrite K by lia. exact (Ht x Hx).
Qed.
Lemma b10s_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------- JOIN at the return state ---------- *)
Lemma b10s_join : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r
  (regsT : bvmap 5 word) memr (fx1 : YK11.FPState) regs2 mem2 md2,
  INV_ROLEV (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (seg_spec.rseg_addr (p_c v) gi + 16 <= a < seg_spec.rseg_addr (p_c v) gi + 24) ->
     rdW Wc memr a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memr a <> None) ->
  sa_val (rdW Wc memr) (seg_spec.rseg_addr (p_c v) gi + 16) 4 r ->
  sa_val (rdW Wc memr) (seg_spec.rseg_addr (p_c v) gi + 20) 4 1 ->
  aregs_preserved rX regsT ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem2 md2 0 ->
  aregs_preserved regsT regs2 ->
  (forall i, 0 <= i < RtPFShared.sn_len (96 - 1) (rc_reading cf) ->
     rdW Wc mem2 (seg_spec.rseg_addr (p_c v) gi + 160 + i) =
     Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (96 - 1) (rc_reading cf)) 0)) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (seg_spec.rseg_addr (p_c v) gi + 160 <= a <
        seg_spec.rseg_addr (p_c v) gi + 160 + RtPFShared.sn_len (96 - 1) (rc_reading cf)) ->
     ~ (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memr a) ->
  INV_JOIN (fx := fx1) B n v pos lyc Sc Wc regs2 mem2 md2
    (r_upd cf gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading cf)]))) nm o ln d gi.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r regsT memr fx1 regs2 mem2 md2
  HI KR PR V16 V20 PRT Hfx HJ3 PRT2 HBY HK3.
destruct HI as (HBASE & HMID & HST & HROLE & HRG).
destruct HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10s_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
pose proof HOBJ as (_ & _ & _ & _ & HC5 & _).
destruct (b10s_cblk B v pos lyc Sc Wc memc mdc HAR Hin EF HTF HC5) as (HCP & bb & mm & Hbin & Hb1 & Hb2).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof HCP as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof HMID as (Ho & _).
assert (Hgi : (gi < length (rc_seg cf))%nat) by exact HCUR.
assert (Hgi32 : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & H32 & _)); lia).
destruct (b10s_reading_str (rdW Wc memc) (p_c v) cf HRC
  ltac:(apply Z.mod_divide in C3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z_mod_mult))
  as (_ & Hsome0 & HTlen & HTnz).
set (T := rc_reading cf) in *.
pose proof (b10s_sn_len T HTlen) as Hsl. pose proof (b10s_sn_bytes T HTlen) as Hsb.
rewrite Hsl in HBY, HK3. rewrite Hsb in HBY.
rewrite (snprintf_s1 96 T HTnz) by lia.
set (cur := seg_spec.rseg_addr (p_c v) gi) in *.
assert (Ecur : cur = p_c v + 356 * Z.of_nat gi) by reflexivity.
unfold RtPFCmd.CMD_SNP_K, ESTACK in HK3.
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
rewrite ESTK in Hpres3.
(* what the piece kept *)
assert (KP01 : b10s_kept v (rdW Wc memc) (rdW Wc memr)).
{ split.
  - intros a Ha Hn. apply KR; [exact Ha|]. intros Hc. apply Hn. left. unfold seg_spec.SEG_C_SIZE. lia.
  - intros a _ Hv. exact (PR a Hv). }
assert (KP12 : b10s_kept v (rdW Wc memr) (rdW Wc mem2)).
{ split.
  - intros a Ha Hn. apply HK3; [exact Ha | intros Hc; apply Hn; left; unfold seg_spec.SEG_C_SIZE; lia |].
    intros Hc. apply Hn. right. lia.
  - intros a Ha Hv.
    destruct (Z_lt_le_dec a (cur + 160)) as [Hlo | Hlo];
    [|destruct (Z_lt_le_dec a (cur + 160 + (Z.of_nat (length T) + 1))) as [Hhi | Hhi]].
    + destruct (Z_lt_le_dec a (pf_s1 v - 8192)) as [Hw | Hw]; [rewrite HK3 by lia; exact Hv|].
      destruct (Z_lt_le_dec a (pf_s1 v)) as [Hw2 | Hw2]; [|rewrite HK3 by lia; exact Hv].
      apply (aview_some_of_apresent SEGS). apply Hpres3. lia.
    + replace a with (cur + 160 + (a - (cur + 160))) by lia. rewrite HBY by lia. discriminate.
    + destruct (Z_lt_le_dec a (pf_s1 v - 8192)) as [Hw | Hw]; [rewrite HK3 by lia; exact Hv|].
      destruct (Z_lt_le_dec a (pf_s1 v)) as [Hw2 | Hw2]; [|rewrite HK3 by lia; exact Hv].
      apply (aview_some_of_apresent SEGS). apply Hpres3. lia. }
pose proof (b10s_kept_trans v _ _ _ KP01 KP12) as KP02.
(* the block's bytes after the piece *)
assert (Hsome2 : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> rdW Wc mem2 x <> None).
{ intros x Hx. apply (proj2 KP02 x); [unfold seg_spec.SEG_C_SIZE in *; lia | exact (Hsome0 x Hx)]. }
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> ~ (cur + 16 <= a < cur + 24) -> ~ (cur + 160 <= a < cur + 256) ->
  a < pf_s1 v - 8192 -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha H1 H2 H3. rewrite HK3 by lia. apply KR; [exact Ha | exact H1]. }
unfold INV_JOIN.
split; [|split; [exact HMID|split]].
- (* pf_base at PF_SC_LOW *)
  split; [exact HCX|].
  split.
  { split; [exact HJ3|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split; [exact (b10s_keep_saved v pos _ _ _ HG HCP KP02 HSAV)|].
    split; [exact (b10s_keep_flag v pos _ _ HG HCP KP02 HFLAG)|].
    split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|]. split; [exact HTF|].
    split.
    { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
      exact (b10s_keep_slot v pos _ _ 0xc8 _ HG HCP KP02 ltac:(lia) HC8). }
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite PRT2 by (unfold acallee_saved; lia); rewrite PRT by (unfold acallee_saved; lia);
       apply (b10s_rg rX _ _ _ HRG0); b10s_in). }
  split; [exact (b10s_keep_obj B v pos lyc Sc Wc memc mdc _ _ HG HCP HCX HAR KP02 HOBJ)|].
  split; [exact (b10s_keep_sl v pos _ _ HG HCP KP02 HSL)|].
  exact (b10s_keep_fsh v pos _ _ _ HG HCP KP02 HFSH).
- (* pf_st *)
  split.
  { apply (b10b_rconf_role (rdW Wc memc) (rdW Wc mem2) (p_c v) cf gi r T HRC Hgi
      ltac:(pose proof (b10b_role_range _ _ HROLE); lia) HTlen HTnz).
    - fold cur. unfold seg_spec.RS_ROLE. intros k Hk. rewrite HK3 by (unfold seg_spec.SEG_C_SIZE in *; lia).
      exact (V16 k Hk).
    - fold cur. unfold seg_spec.RS_ROLE_SET. intros k Hk. rewrite HK3 by (unfold seg_spec.SEG_C_SIZE in *; lia).
      exact (V20 k Hk).
    - fold cur. unfold seg_spec.RS_ROLE_FILE.
      exists (b10f_view (rdW Wc mem2) (cur + 160) 96). split.
      + apply b10f_view_bytes. intros i Hi.
        destruct (rdW Wc mem2 (cur + 160 + Z.of_nat i)) as [z|] eqn:Ez.
        * exists z. split; [reflexivity | exact (b10s_val_range _ _ _ _ _ Ez)].
        * exfalso. apply (Hsome2 (cur + 160 + Z.of_nat i)); [unfold seg_spec.SEG_C_SIZE; lia | exact Ez].
      + unfold seg_spec.cstr_enc. split; [apply b10f_view_len|]. split; [lia|]. split; [exact HTnz|].
        apply nth_ext with (d := 0) (d' := 0).
        { rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, b10f_view_len. cbn [length]. lia. }
        intros i Hi. rewrite length_firstn in Hi. unfold seg_spec.zs in Hi. rewrite length_map, b10f_view_len in Hi.
        rewrite nth_firstn. destruct (Nat.ltb_spec i (S (length T))) as [_|]; [|lia].
        rewrite b10f_nth_zs by (rewrite b10f_view_len; lia). rewrite b10f_view_nth by lia.
        pose proof (HBY (Z.of_nat i) ltac:(lia)) as Ei. rewrite Nat2Z.id in Ei. rewrite Ei. cbn [b10f_o0].
        apply b10f_unsigned_small. exact (b10s_val_range _ _ _ _ _ Ei).
    - intros i Hi H1 H2 H3. fold cur in H1, H2, H3.
      unfold seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_ROLE_FILE, seg_spec.SEG_C_SIZE in *.
      apply K2c; lia. }
  split; [unfold pf_cur_ok in *; rewrite b10b_upd_len; exact HCUR|].
  split; [exact (b10s_keep_nm v pos _ _ nm HG HCP KP02 HNM)|].
  split.
  { apply (pf_cnt_mono _ (length (skipn o (p_s v)))); [pose proof (pf_next_skipn_lt (p_s v) o Ho); lia|].
    unfold pf_cnt in *. rewrite b10b_upd_refused, b10b_upd_overflow. exact HCNT. }
  exact (b10s_keep_slot v pos _ _ 0xc0 _ HG HCP KP02 ltac:(lia) HC0).
- unfold PF_RL, PF_RM in *. unfold pf_rg. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite PRT2 by (unfold acallee_saved; lia); rewrite PRT by (unfold acallee_saved; lia);
     apply (b10s_rg rX _ _ _ HRG); b10s_in).
Qed.

(* ---------- the call 0x88dc4 snprintf(cur + 0xa0, 96, 0x21340 "%s", c + RC_READING) to H_JOIN at fx1 ---------- *)
Lemma b10s_from_call : forall n, HA_JOIN B n ->
  forall v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r (regsT : bvmap 5 word) memr mdr,
  INV_ROLEV (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memr mdr 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (seg_spec.rseg_addr (p_c v) gi + 16 <= a < seg_spec.rseg_addr (p_c v) gi + 24) ->
     rdW Wc memr a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memr a <> None) ->
  sa_val (rdW Wc memr) (seg_spec.rseg_addr (p_c v) gi + 16) 4 r ->
  sa_val (rdW Wc memr) (seg_spec.rseg_addr (p_c v) gi + 20) 4 1 ->
  aregs_preserved rX regsT ->
  getr regsT 1 = Z_to_bv 64 (BASE + PF_JOIN) ->
  getr regsT 10 = w64 (seg_spec.rseg_addr (p_c v) gi + 160) ->
  getr regsT 11 = w64 96 ->
  getr regsT 12 = w64 0x21340 ->
  getr regsT 13 = w64 (p_c v + seg_spec.RC_READING) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memr (seg_rom SEGS)) mdr)
    (pf_postm B v (r_upd cf gi (rs_with_role r (snprintf_s 96 F_s [AS (rc_reading cf)])), Some gi, nm) o ln).
Proof.
intros n HJN v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r regsT memr mdr HI HJr KR PR V16 V20 PRT R1 R10 R11 R12 R13.
pose proof HI as (HBASE & HMID & HST & HROLE & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10s_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof HST as (HRC & HCUR & HNM & HCNT & HC0).
pose proof HOBJ as (_ & _ & _ & _ & HC5 & _).
destruct (b10s_cblk B v pos lyc Sc Wc memc mdc HAR Hin EF HTF HC5) as (HCP & bb & mm & Hbin & Hb1 & Hb2).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof HCP as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof pf_B_values as (_ & _ & _ & Egw & Egd & _ & _ & _ & _ & _ & Elit).
assert (Hgi : (gi < length (rc_seg cf))%nat) by exact HCUR.
assert (Hgi32 : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & H32 & _)); lia).
assert (C8 : p_c v mod 8 = 0)
  by (apply Z.mod_divide in C3 as [q Hq]; [|lia]; rewrite Hq; replace (q * 16) with ((2 * q) * 8) by lia; apply Z_mod_mult).
destruct (b10s_reading_str (rdW Wc memc) (p_c v) cf HRC C8) as (HSTR0 & Hsome0 & HTlen & HTnz).
set (T := rc_reading cf) in *.
set (cur := seg_spec.rseg_addr (p_c v) gi) in *.
assert (Ecur : cur = p_c v + 356 * Z.of_nat gi) by reflexivity.
pose proof HJr as (HARr & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_READING in *.
(* the cut's objects at the call *)
assert (KP01 : b10s_kept v (rdW Wc memc) (rdW Wc memr)).
{ split.
  - intros a Ha Hn. apply KR; [exact Ha|]. intros Hc. apply Hn. left. unfold seg_spec.SEG_C_SIZE. lia.
  - intros a _ Hv. exact (PR a Hv). }
pose proof (b10s_keep_obj B v pos lyc Sc Wc memc mdc _ _ HG HCP HCX HAR KP01 HOBJ) as HOBJ1.
pose proof HOBJ1 as (_ & _ & _ & HC4r & _ & _ & HLITr & HRODr & HSSPr).
(* c->reading at the call *)
assert (HSTR1 : sa_str (rdW Wc memr) (p_c v + 16512) T).
{ apply (b10s_str_keep (rdW Wc memc)); [exact HSTR0|]. intros x Hx. apply KR; lia. }
(* the format "%s" at 0x21340 *)
pose proof (HLITr F_s ltac:(unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity)) as HLF.
rewrite Elit in HLF. destruct HLF as (_ & HFS & HFP & _ & _).
pose proof (HFP lyc Sc Wc memr mdr HARr) as HFA. rewrite b10s_F_s_len in HFA. cbn [Z.add] in HFA.
(* the registers *)
assert (R2 : getr regsT 2 = w64 (pf_s1 v)).
{ apply (b10s_bvr _ _ 2); [reflexivity|]. rewrite PRT by (unfold acallee_saved; lia). apply (b10s_rg rX _ _ _ HRG0). b10s_in. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ apply (b10s_bvr _ _ 3); [reflexivity|]. rewrite PRT by (unfold acallee_saved; lia). apply (b10s_rg rX _ _ _ HRG0). b10s_in. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ apply (b10s_bvr _ _ 4); [reflexivity|]. rewrite PRT by (unfold acallee_saved; lia). apply (b10s_rg rX _ _ _ HRG0). b10s_in. }
assert (Hsp : spZ regsT = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the block's range facts at the call *)
destruct (b10s_addr_sub _ _ _ (cur + 160) 96 HC4r ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE; lia) ltac:(lia))
  as (_ & _ & Hamd & HRAd & HHVd).
pose proof (b10s_addr_sub _ _ _ (p_c v + 16512) (Z.of_nat (length T) + 1) HC4r ltac:(lia)
  ltac:(unfold seg_spec.SEG_C_SIZE; lia) ltac:(lia)) as HAw.
pose proof HC4r as (_ & _ & HAMc & _).
unfold pf_postm, PF_POSTr.
eapply srr_after_artF.
{ apply (b10s_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (pa_sigma SS___interceptor_trampoline_snprintf)
    (ASNP fx) Wc regsT memr STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdr 0 (cur + 160) 96 0x21340 T (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + PF_JOIN)) HJr R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - exact (b10s_m16 _ _ S6 S3).
  - lia.
  - unfold RtPFCmd.CMD_SNP_K, ESTACK. rewrite ESTK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold PF_JOIN, AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split.
    + right; left. split.
      * exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [left; reflexivity|]. cbn [fst snd]. unfold seg_spec.RC_N. lia.
      * exists bb, mm. split; [exact Hbin | unfold seg_spec.SEG_C_SIZE in *; lia].
    + unfold RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - intros a Ha _ [(_ & Hia) | Hsp0]; exfalso; [pose proof (pa_img_range a Hia); unfold kImgEnd in *; lia | lia].
  - unfold amem_range, seg_spec.SEG_C_SIZE in *. lia.
  - exact HRAd.
  - exact (HHVd ltac:(lia)).
  - unfold off_img. rewrite b10s_sn_len by exact HTlen. lia.
  - unfold RtPFCmd.CMD_IMG_HI, RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd. lia.
  - exact HSSPr.
  - rewrite Egw. lia.
  - rewrite Egw. unfold RtPFCmd.CMD_IMG_HI, kImgEnd. lia.
  - rewrite Egd. lia.
  - rewrite Egd. unfold RtPFCmd.CMD_IMG_HI, kImgEnd. lia.
  - rewrite Egw. unfold RtPFCmd.CMD_IMG_LO. lia.
  - rewrite Egd. unfold RtPFCmd.CMD_IMG_LO. lia.
  - apply (b10s_FR_s_regs (rdW Wc memr) _ 0x21340 (p_c v + 16512) T regsT).
    + unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R13. unfold w64. apply unsigned_lit_small. lia.
    + lia.
    + unfold RtPFCmd.CMD_IMG_LO. lia.
    + unfold RtPFCmd.CMD_GOTW. lia.
    + exact HFS.
    + exact HFA.
    + unfold RtPFShared.snp_out. rewrite Hsp, b10s_sn_len by exact HTlen.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        unfold zdisjoint; cbn [fst snd]; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
    + lia.
    + exact (b10s_bytes_range_aview SEGS (w_H Wc) memr _ T HSTR1).
    + lia.
    + exact HSTR1.
    + exact HAw.
    + unfold amem_range, seg_spec.SEG_C_SIZE in *. lia.
    + unfold RtPFShared.snp_out. rewrite Hsp, b10s_sn_len by exact HTlen.
      pose proof (Z.mod_pos_bound (- (p_c v + 16512 + Z.of_nat (length T) + 1)) 8 ltac:(lia)).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        unfold zdisjoint, seg_spec.cstr_span; cbn [fst snd]; unfold RtPFCmd.CMD_SNP_K, ESTACK in *; lia.
  - lia.
  - intros a (sg & Hsg & Hw & Hr) Ho He. exact (HRODr a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
  - exact HFRM. }
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ3 & PRT2 & _ & HBY & HK3 & _ & _).
apply (HJN fx1 v pos lyc Sc Wc regs2 mem2 md2 (r_upd cf gi (rs_with_role r (snprintf_s 96 F_s [AS T]))) nm o ln d gi).
apply (b10s_join n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r regsT memr fx1 regs2 mem2 md2 HI KR PR V16 V20 PRT
  Hfx HJ3 PRT2 HBY).
intros a Ha H1 H2. apply HK3; [exact Ha | exact H1 | lia].
Qed.
End x.
End d.
