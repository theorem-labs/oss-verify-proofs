(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the three exit cuts of segment B8a of
   reac_segconf_parse_file's walk (lib/B/Prog/pf_pieces.v S_B8a), rebuilt from SEG's cut and a later state of the
   segment. The B8a segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: cut lemmas, no instruction walked).
     NEW   0x88e54  b8_new_ok    from `blez a2` 0x88cb8 (n = 0) or `blt a2,s3` 0x88d38 (n < 32, no entry has the
                                 name): a2 = n, a3 = sh(c + 0x2c80), s3 = 32, s7 = the name
     FOUND 0x88eb0  b8_found_ok  from `beqz a0` 0x88d08 (strcmp = 0): s3 = &seg[i], s7 = &seg[i].seen_gen, slot 0xc0
                                 = the name (0x88cc0)
     REFTL 0x887cc  b8_reftl_ok  from `j` 0x88d64 (32 entries, none has the name): c->overflow + 1 stored (0x88d54),
                                 a2 = F_bound's literal (0x88d58 / 0x88d5c), a4 = 32, s7 = the name (0x88d2c)
   Each holds when the state's journal goes on from parse_file's entry and its memory agrees with SEG's off B8a's
   write set (pf_seg_B8a_m.v b8_W). The structure is the image-A G3 walk owner's A8a kit's (lib/A/Prog/pf_a8a_k.v a8c / a8c_keep,
   commit 61a728170142): INV_SEG's facts less the registers the segment overwrites. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YP03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B8a_k pf_seg_B8a_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma b8_rg_incl : forall rX L1 L2, pf_rg rX L1 -> incl L2 L1 -> pf_rg rX L2.
Proof. intros rX L1 L2 H Hi. unfold pf_rg in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hi x Hx)). Qed.
Ltac b8_incl := let x := fresh "x" in let Hx := fresh "Hx" in
  unfold PF_RL, PF_RM, b8_FI; cbn [app]; intros x Hx; cbn [In] in Hx |- *; tauto.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

Section s.
Variables (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
  (np : Z) (name : list Z).
Hypothesis HSEG : INV_SEG B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name.
Variables (rY : bvmap 5 word) (memY : word -> option byte) (mdY : Model).
Hypothesis HJ : ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
  (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memY mdY 0.

Lemma b8_new_ok : b8_keep v false (rdW Wc memc) (rdW Wc memY) ->
  pf_rg rY (b8_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++
            [(12, Z.of_nat (length (rc_seg cf))); (13, shadow_addr (p_c v + seg_spec.RC_N)); (19, 32); (23, np)]) ->
  r_find_go (rc_seg cf) name 0 = None -> (length (rc_seg cf) < 32)%nat ->
  INV_NEW B n v pos lyc Sc Wc rY memY mdY cf nm o ln d np name.
Proof using HSEG HJ.
intros HK HR HF HL32.
destruct HSEG as (HB & HM & (HRC & HNM & HCNT) & HS & HI & HL & _).
split; [apply (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false rY memY mdY HB HJ HK); apply (b8_rg_incl _ _ _ HR); b8_incl|].
split; [exact HM|].
split; [split; [exact (b8_keep_rconf B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB HK cf eq_refl HRC)|
               split; [exact (b8_keep_nm B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB HK nm HNM) | exact HCNT]]|].
split; [exact (b8_keep_buf_str B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB HK np name HI HS)|].
split; [exact HI|]. split; [exact HL|]. split; [exact HF|]. split; [exact HL32|].
apply (b8_rg_incl _ _ _ HR); b8_incl.
Qed.

Lemma b8_found_ok : forall i, b8_keep v false (rdW Wc memc) (rdW Wc memY) ->
  pf_sl (rdW Wc memY) (pf_s1 v) [(0xc0, np)] ->
  pf_rg rY (b8_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++
            [(19, seg_spec.rseg_addr (p_c v) i); (23, seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN)]) ->
  r_find_go (rc_seg cf) name 0 = Some i ->
  INV_FOUND B n v pos lyc Sc Wc rY memY mdY cf nm o ln d np name i.
Proof using HSEG HJ.
intros i HK HSL HR HF.
destruct HSEG as (HB & HM & (HRC & HNM & HCNT) & HS & HI & HL & _).
split; [apply (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false rY memY mdY HB HJ HK); apply (b8_rg_incl _ _ _ HR); b8_incl|].
split; [exact HM|].
split; [split; [exact (b8_keep_rconf B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB HK cf eq_refl HRC)|
               split; [exact (b8_keep_nm B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB HK nm HNM) | exact HCNT]]|].
split; [exact (b8_keep_buf_str B v pos lyc Sc Wc rX memc mdc PF_SC_LINE false memY HB HK np name HI HS)|].
split; [exact HI|]. split; [exact HL|]. split; [exact HF|]. split; [exact HSL|].
apply (b8_rg_incl _ _ _ HR); b8_incl.
Qed.

Lemma b8_reftl_ok : b8_keep v true (rdW Wc memc) (rdW Wc memY) ->
  sa_val (rdW Wc memY) (p_c v + seg_spec.RC_OVERFLOW) 4 (rc_overflow cf + 1) ->
  pf_rg rY (b8_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++ [(12, seg_litA_rc F_bound); (14, 32); (23, np)]) ->
  INV_REFTL B n v pos lyc Sc Wc rY memY mdY (b8_ovf cf) nm o ln d F_bound (seg_litA_rc F_bound) 32 np name.
Proof using HSEG HJ.
intros HK HV HR.
pose proof HSEG as (HB & HM & (HRC & HNM & HCNT) & HS & HI & HL & _).
destruct (b8_reftl_cnt (p_s v) o cf (proj1 HM) HCNT) as (C1 & C2 & C3).
split; [apply (b8_move B v pos lyc Sc Wc rX memc mdc PF_SC_LINE true rY memY mdY HB HJ HK); apply (b8_rg_incl _ _ _ HR); b8_incl|].
split; [exact HM|].
split.
{ split.
  - apply (b8_sa_rconf_ovf (rdW Wc memc) (rdW Wc memY) (p_c v) cf HRC C3); [|exact HV].
    intros a Ha Hn. destruct (b8_c_blk B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (bc & mc & _ & Hc1 & Hc2 & Hc4 & Hc3 & _).
    apply (b8_low B v pos lyc Sc Wc rX memc mdc PF_SC_LINE true memY HB HK); unfold seg_spec.SEG_C_SIZE in *; lia.
  - split; [exact (b8_keep_nm B v pos lyc Sc Wc rX memc mdc PF_SC_LINE true memY HB HK nm HNM) | exact C1]. }
split; [exact C2|].
split; [split; [right; split; reflexivity | reflexivity]|].
split; [exact (b8_keep_buf_str B v pos lyc Sc Wc rX memc mdc PF_SC_LINE true memY HB HK np name HI HS)|].
split; [exact HI|].
apply (b8_rg_incl _ _ _ HR); b8_incl.
Qed.
End s.
End e.
End f.
End d.
