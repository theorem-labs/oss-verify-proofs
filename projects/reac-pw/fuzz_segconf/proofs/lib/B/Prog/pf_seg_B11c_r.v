(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the F_badmodel
   refuse call site of segment B11c of reac_segconf_parse_file's walk (jal 0x892f8 at 0x88bec), as one closed
   lemma: the state at the call supplies every premise refuse_contract (lib/B/Prog/refuse_c.v) asks besides
   afn_pre. The B11c segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: call-site lemma).
   ADAPTED from the image-A G3 walk owner's image-A refuse site rule lib/A/Prog/pf_a7_s.v (commit
   ebe0b30cca65: a7_refuse_site_ok, a7_va_ok, a7_apart, a7_room_ev) and the A11b facts lib/A/Prog/pf_a11b_f.v
   (commit 95f85b0d718c: pf_lit_badmodel, pf_badmodel_fmt, pf_badmodel_kinds), re-derived
   for image B's site and its three string arguments, all in the class-5 frame F:
     a0 = c (slot 0xc8, 0x88bd8), a1 = s6 = lineno = ln + 1 (0x88bdc), a2 = F_badmodel's literal 0x21880 (.str.20,
     0x88bd0 auipc / 0x88bd4 addi), a3 = slot 0x40 = cur_name F + 0x20 (0x88be0), a4 = slot 0x70 = val in buf
     (0x88be4), a5 = slot 0x78 = known F + 0x320 (0x88be8); sp = s1.
   WHERE EACH PREMISE COMES FROM (INV_KCALL below, the cut KREFM's state with the call's registers):
   - each %s argument: its bytes and NUL addressable (sa_addr) because their shadow cells are 0 while cur_name,
     buf and known are in scope (PF_SC_KNOWN; pf_seg_B11c_k.v b11_addr_frame), its read span (to the next 8-byte
     boundary: cur_name ends at F + 0x30, buf at F + 0x240, the span of known at F + 0x370) inside the frame, which
     lies below alloc_ceiling <= ly_stk_lo and apart from the block c (YCbq.sep_block_frame), and the frame live
     (sa_fframe, refuse_va_locs' frame arm). cur_name's C string from pf_nm (seg_spec.cstr_enc 16).
   - c: c <> 0, 16-aligned (pf_tf), its bytes, block and addressability (pf_st, pf_obj); rc_refused cf + 1 < 2 ^ 32
     from pf_cnt; the slot refusal[n] (n <= 8, rconf_enc) and c->refused inside the block.
   - lineno: pf_lctx's ln + 1 <= pf_next s o <= length s <= 65535 (pf_tf).
   - the format and literals, the read-only view, printf's cells: pf_obj; sa_frm0: pf_fi.
   - sa_room and the events: the journal's frames / events clauses with pf_cx's sa_room_n 2 and event bound.
   No UBSan trap branch and no inline check in 0x88bd0-0x88bec. Section hypotheses: none. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11c_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------- the format and its literal ---------- *)
Lemma b11_lit_badmodel : seg_litA_rc F_badmodel = 0x21880.
Proof. vm_compute. reflexivity. Qed.
Lemma b11_in_lits_badmodel : In F_badmodel PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma b11_badmodel_fmt : In F_badmodel seg_spec.REFUSE_FORMATS.
Proof. unfold seg_spec.REFUSE_FORMATS. cbn [In]. tauto. Qed.
Lemma b11_badmodel_kinds : forall nm val k : list Z,
  seg_spec.conv_kinds F_badmodel = map seg_spec.arg_is_s [AS nm; AS val; AS k].
Proof. intros nm val k. vm_compute. reflexivity. Qed.
Lemma b11_known_len : length known = 77%nat.
Proof. vm_compute. reflexivity. Qed.

(* ---------- lists and numbers ---------- *)
Lemma b11_nth_firstn : forall {A} n (l : list A) k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  intros A n. induction n as [|n IH]; intros l k d Hk; [lia|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [firstn].
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
(* reader_pre's text bound (length s <= 65535)%nat, in Z *)
Lemma b11_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
  intros m H. apply Nat2Z.inj_le in H.
  assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
  rewrite E in H. exact H.
Qed.
(* rounding up to the next multiple of 8 stays below an 8-aligned bound *)
Lemma b11_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
  intros x M H1 H2.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
  lia.
Qed.
(* cur_name's C string (seg_spec.cstr_enc 16): its bytes, NUL and slack are the field's 16 bytes *)
Lemma b11_nm_str : forall (rd : reader) a nm, a mod 8 = 0 -> pf_nm rd a nm ->
  sa_str rd a nm /\ (length nm < 16)%nat.
Proof.
  intros rd a nm Ha (f & Hb & Hl & Hn & Hz & Hf).
  assert (Hnth : forall i, (i < 16)%nat -> rd (a + Z.of_nat i) = Some (nth i (seg_spec.zs f) 0)).
  { intros i Hi. rewrite (Hb i ltac:(lia)). f_equal. unfold seg_spec.zs.
    rewrite <- (map_nth bv_unsigned f ZB0 i). apply nth_indep. rewrite length_map. lia. }
  split; [|exact Hn].
  split; [split; [|exact Hz]|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (Hnth i ltac:(lia)). f_equal. rewrite <- Hf. rewrite b11_nth_firstn by lia. reflexivity.
  - intros x Hx.
    pose proof (Z.div_mod (a + Z.of_nat (length nm)) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (a + Z.of_nat (length nm)) 8 ltac:(lia)) as M.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Ha in Da.
    replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
    rewrite (Hnth (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.

(* a register named by a bv literal is the one pf_rg names by its number *)
Lemma b11_bvr : forall (rr : bvmap 5 word) (r : bv 5) k x, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = x -> getr rr r = x.
Proof. intros rr r k x Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** *** KCALL (the jal at 0x88bec): KREFM's state with the call's argument registers *)
Definition B11_ARGS (v : pfv) (pos : Z) (ln vp : Z) : list (Z * Z) :=
  [(10, p_c v); (11, ln + 1); (12, seg_litA_rc F_badmodel); (13, pf_F v pos + PF_O_CN); (14, vp);
   (15, pf_F v pos + PF_O_KNOWN)].
Definition INV_KCALL (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (vp : Z) (val : list Z) : Prop :=
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_KNOWN /\ pf_mid v o ln d n /\
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) /\
  sa_str (rdW Wc memc) vp val /\ pf_inb (pf_F v pos + PF_O_BUF) vp val /\
  sa_str (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) known /\
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++ B11_ARGS v pos ln vp).

(* refuse_contract at image B's numbers, at the F_badmodel call: what it asks besides afn_pre *)
Definition b11_refuse_call (v : pfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (regs : bvmap 5 word) (cf : rconf) (ln : Z) (args : list arg) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 (p_c v) /\ 0 <= p_c v < 2 ^ 64 /\
  getr regs 11 = w64 (ln + 1) /\ 0 <= ln + 1 < 2 ^ 64 /\
  getr regs 12 = w64 (seg_litA_rc F_badmodel) /\ 0 <= seg_litA_rc F_badmodel < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regs (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc F_badmodel)
    [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] cf (ln + 1) F_badmodel args /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.

(* one %s argument in the class-5 frame whose cells are 0 and whose 8-rounded span ends at M *)
Lemma b11_va_frame : forall v pos lyc Sc (Wc : world SEGS) memc mdc sc (rd : reader) q s sp (k : nat) M,
  b11_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_fsh rd (pf_SH v pos) sc -> sa_str rd q s -> (length s <= 65535)%nat ->
  pf_F v pos + 32 <= q -> q + Z.of_nat (length s) + 1 <= M -> M mod 8 = 0 -> M <= pf_F v pos + 1088 ->
  (forall x, q <= x < q + (Z.of_nat (length s) + 1) -> pf_shb sc ((x - pf_F v pos) / 8) = 0) ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE -> (k <= 8)%nat -> alloc_ceiling <= ly_stk_lo lyc ->
  sa_va_arg rd
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)] (w64 q) (AS s) /\
  sa_fframe lyc Sc q (Z.of_nat (length s) + 1).
Proof.
intros v pos lyc Sc Wc memc mdc sc rd q s sp k M HG HAR Hin EF HF HS HL Hq HM HM8 HMF HZ Hc Hk Hceil.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
assert (EQ : bv_unsigned (w64 q) = q) by (apply b11_w64_u; lia).
split; [|apply (b11_fframe v pos lyc Sc q _ Hin EF); lia].
cbn [sa_va_arg]. rewrite EQ.
split; [lia|]. split; [exact HS|]. split; [exact HL|].
split; [apply (b11_addr_frame v pos rd sc q (Z.of_nat (length s) + 1) HG HF Hq ltac:(lia) ltac:(lia) HZ)|].
(* the span stays in the frame, below the stack and apart from the block c *)
pose proof (b11_round8 (q + Z.of_nat (length s) + 1) M HM HM8) as HR.
assert (HSP : q + seg_spec.cstr_span q s <= M) by (unfold seg_spec.cstr_span; lia).
destruct Hc as (b & m & Hb & Hb1 & Hb2).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hsep.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hrq].
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EF in Hsep. change (fs_frame_bytes 5) with 2048 in Hsep.
assert (HAP : q + seg_spec.cstr_span q s <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= q)
  by (destruct Hsep as [Hs|Hs]; [right|left]; lia).
unfold sa_apart_all, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
  seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *.
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_cons; [cbn [fst snd]; lia|].
apply Forall_nil.
Qed.

(* the site: INV_KCALL gives refuse_contract's premises besides afn_pre *)
Lemma b11_refuse_site : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_KCALL n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  b11_refuse_call v lyc Sc Wc memc rX cf ln [AS nm; AS val; AS known].
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
destruct HI as (HBASE & HMID & HST & HVS & HVI & HKS & HRG).
destruct HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HSLC & HRG0).
pose proof HTF as (C0 & C16 & _ & _ & LS).
pose proof HCX as (_ & _ & _ & HcB & _ & _ & _ & _ & _ & HROOM & HEV).
pose proof HOBJ as (_ & _ & _ & Ac & Hc & _ & LITS & HROD & SSP).
pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (_ & _ & Hceil & _).
rewrite <- Hly in Hceil.
destruct HMID as (Ho & Hle & Hlctx).
destruct Hlctx as (Hon & _ & Hlnd & Hlno).
destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
pose proof HRC as (bs & _ & (_ & _ & _ & _ & HK8 & _)).
pose proof (b11_le65535 _ LS) as LSZ.
assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
pose proof asan_consts as (AC1 & _).
assert (Hvalid : forall r x, In (r, x) (B11_ARGS v pos ln vp) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x Hrx; apply (b11_rg rX _ r x HRG); apply in_or_app; right; apply in_or_app; right; exact Hrx).
assert (R10 : getr rX 10 = w64 (p_c v))
  by (apply (b11_bvr rX _ 10); [reflexivity | apply Hvalid; unfold B11_ARGS; b11_in]).
assert (R11 : getr rX 11 = w64 (ln + 1))
  by (apply (b11_bvr rX _ 11); [reflexivity | apply Hvalid; unfold B11_ARGS; b11_in]).
assert (R12 : getr rX 12 = w64 (seg_litA_rc F_badmodel))
  by (apply (b11_bvr rX _ 12); [reflexivity | apply Hvalid; unfold B11_ARGS; b11_in]).
assert (R13 : getr rX 13 = w64 (pf_F v pos + PF_O_CN))
  by (apply (b11_bvr rX _ 13); [reflexivity | apply Hvalid; unfold B11_ARGS; b11_in]).
assert (R14 : getr rX 14 = w64 vp)
  by (apply (b11_bvr rX _ 14); [reflexivity | apply Hvalid; unfold B11_ARGS; b11_in]).
assert (R15 : getr rX 15 = w64 (pf_F v pos + PF_O_KNOWN))
  by (apply (b11_bvr rX _ 15); [reflexivity | apply Hvalid; unfold B11_ARGS; b11_in]).
pose proof (LITS F_badmodel b11_in_lits_badmodel) as HLF.
(* the three strings *)
assert (HF8 : pf_F v pos mod 8 = 0).
{ pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D. rewrite F3 in D.
  replace (pf_F v pos) with ((4 * (pf_F v pos / 32)) * 8) by lia. apply Z_mod_mult. }
assert (F8 : (pf_F v pos + PF_O_CN) mod 8 = 0) by (rewrite Zplus_mod, HF8; reflexivity).
destruct (b11_nm_str _ _ nm F8 HNM) as [HNS HNL].
destruct HVI as [HV1 HV2].
assert (HZ0 : forall lo hi x, (4 <= lo /\ hi <= 6) \/ (8 <= lo /\ hi <= 72) \/ (100 <= lo /\ hi <= 130) ->
    pf_F v pos + 8 * lo <= x < pf_F v pos + 8 * hi -> pf_shb PF_SC_KNOWN ((x - pf_F v pos) / 8) = 0).
{ intros lo hi x Hlh Hx. apply b11_shb_known0.
  assert (Q1 : lo <= (x - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Q2 : (x - pf_F v pos) / 8 < hi) by (apply Z.div_lt_upper_bound; lia).
  lia. }
pose proof b11_known_len as KL.
assert (VA1 := b11_va_frame v pos lyc Sc Wc memc mdc PF_SC_KNOWN (rdW Wc memc) (pf_F v pos + PF_O_CN) nm
  (spZ rX) (length (rc_refusal cf)) (pf_F v pos + 0x30) HGEO HAR Hin EF HFSH HNS
  ltac:(apply (Nat.le_trans _ 16); [lia | apply Nat.leb_le; vm_compute; reflexivity])
  ltac:(unfold PF_O_CN; lia) ltac:(unfold PF_O_CN; lia)
  ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)
  ltac:(intros x Hx; apply (HZ0 4 6); [left; lia | unfold PF_O_CN in Hx; lia]) Hc HK8 Hceil).
assert (VA2 := b11_va_frame v pos lyc Sc Wc memc mdc PF_SC_KNOWN (rdW Wc memc) vp val
  (spZ rX) (length (rc_refusal cf)) (pf_F v pos + 0x240) HGEO HAR Hin EF HFSH HVS
  ltac:(apply (Nat.le_trans _ 512); [unfold PF_O_BUF in HV1, HV2; lia | apply Nat.leb_le; vm_compute; reflexivity])
  ltac:(unfold PF_O_BUF in HV1; lia) ltac:(unfold PF_O_BUF in HV2; lia)
  ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)
  ltac:(intros x Hx; apply (HZ0 8 72); [right; left; lia | unfold PF_O_BUF in HV1, HV2; lia]) Hc HK8 Hceil).
assert (VA3 := b11_va_frame v pos lyc Sc Wc memc mdc PF_SC_KNOWN (rdW Wc memc) (pf_F v pos + PF_O_KNOWN) known
  (spZ rX) (length (rc_refusal cf)) (pf_F v pos + 0x370) HGEO HAR Hin EF HFSH HKS
  ltac:(rewrite KL; apply Nat.leb_le; vm_compute; reflexivity)
  ltac:(unfold PF_O_KNOWN; lia) ltac:(unfold PF_O_KNOWN; rewrite KL; lia)
  ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)
  ltac:(intros x Hx; apply (HZ0 100 130); [right; right; lia | unfold PF_O_KNOWN in Hx; rewrite KL in Hx; lia])
  Hc HK8 Hceil).
destruct VA1 as [VA1 FF1]. destruct VA2 as [VA2 FF2]. destruct VA3 as [VA3 FF3].
unfold b11_refuse_call.
split; [exact HROD|]. split; [exact R10|]. split; [exact HcB|].
split; [exact R11|]. split; [lia|]. split; [exact R12|]. split; [rewrite b11_lit_badmodel; lia|].
split.
2: { split.
     - unfold sa_room. unfold sa_room_n in HROOM. rewrite Hfr, length_app. cbn [length]. lia.
     - unfold EV_refuse. unfold EV_reac_segconf_parse_file in HEV. lia. }
unfold refuse_pre.
split; [exact C0|]. split; [exact C16|]. split; [exact HRC|]. split; [exact Hc|]. split; [exact Ac|].
split; [destruct HCNT as [HC1 _]; lia|].
split; [exact HLN|]. split; [reflexivity|].
split; [exact b11_badmodel_fmt|]. split; [apply b11_badmodel_kinds|].
split; [rewrite b11_lit_badmodel; lia|]. split; [reflexivity|]. split; [exact HLF|].
split.
{ rewrite R13, R14, R15. cbn [sa_va_args]. split; [exact VA1|]. split; [exact VA2|]. split; [exact VA3 | exact I]. }
split.
{ rewrite R13, R14, R15. cbn [refuse_va_locs].
  rewrite (b11_w64_u (pf_F v pos + PF_O_CN)) by (unfold PF_O_CN; lia).
  rewrite (b11_w64_u vp) by (unfold PF_O_BUF in HV1, HV2; lia).
  rewrite (b11_w64_u (pf_F v pos + PF_O_KNOWN)) by (unfold PF_O_KNOWN; lia).
  split; [right; exact FF1|]. split; [right; exact FF2|]. split; [right; exact FF3 | exact I]. }
split; [exact HFRM|]. split; [exact SSP|].
intros x Hx. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hx.
Qed.
End d.
