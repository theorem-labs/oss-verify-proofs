(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B3 of reac_segconf_parse_file's
   walk, its first piece: FRAME (0x88074) -> the snprintf at 0x880cc -> MID1 (0x880d0). The B3 segment lane of
   the image-B G3 walk owner, 2026-10-30. ADAPTED from the image-A G3 walk owner's image-A segment walk lib/A/Prog/pf_a2.v (commit
   3f59c8d75ed4: the seed from a cut, the run, the call step, the next state) and its snprintf step pf_a8b_t.v
   (here pf_seg_B3_t.v), re-derived on image B's code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     0x88074 ld a0,200(s1); 0x88078 bnez a0 -> 0x88080, else 0x8807c j unimp 0x891c8        UBSan trap T01 (c NULL)
     0x88080 ld a0,200(s1); andi a0,a0,7; 0x88088 beqz a0 -> 0x88090, else 0x8808c j unimp  UBSan trap T02 (c misaligned)
     0x88090 .. 0x880a8 s6 = c + 0x40e0, s7 = c + 0x4080 (slot 0xc8 = c)
     0x880ac bnez s3 -> 0x880b8, else 0x880b0/b4 s3 = .str.1 0x21360 "reac-pw.conf" (listing object 34)
     0x880b8/bc a2 = .str 0x21340 "%s" (object 35); a1 = 96; a0 = s7; a3 = s3
     0x880cc jal snprintf (the listing's pa_sigma SS___interceptor_trampoline_snprintf; return 0x880d0)
   The traps: the seed's fact on atom 32 (c, in [16, 2 ^ 64 - 16] and 16-aligned: pf_tf's c <> 0, c mod 16 = 0, with
   reader_pre's 0 <= c) decides both branches not taken in the token run (YP0m decide_cond, s_and_ptr). The label
   branch: the seed pins s3 = 0 when the label is None (sa_ostr) and gives atom 19 the fact lp >= 1 when it is
   Some (sa_ostr's lp <> 0), so the run decides it too.
   The call is pf_seg_B3_t.v's b3t_aj_snprintf_atSF (row 4, RtFormat.asnprintf_realizes, at every FP state): the
   destination c->reading lies in the block c and in the footprint RC_PARSE_W c; the label's 8 bytes past its NUL
   are pf_seg_B3_k.v's pb3_lab_amem (no new premise). The record after it is pf_seg_B3_f.v's b3f_rconf_reading. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B3_f pf_seg_B3_t pf_seg_B3_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pb3_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the shadow hull of a sub-range lies in the hull of the range (lib/B/Prog/trim_s.v tr_hull_sub) *)
Lemma pb3_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
  shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 Hn s Hs. apply H.
pose proof (Z.div_le_mono (shadow_addr x) (shadow_addr x') 8 ltac:(lia) (shadow_mono x x' H1)) as D1.
pose proof (Z.div_le_mono (shadow_addr (x' + n' - 1)) (shadow_addr (x + n - 1)) 8 ltac:(lia)
  (shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia))) as D2.
lia.
Qed.
(* a reader that agrees on every address keeps a C string and an addressable range *)
Lemma pb3_same_str : forall (rd rd' : reader) p s, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  0 <= p -> p + Z.of_nat (length s) + 8 <= 2 ^ 64 -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s HK H0 H1 [[Hz Hn] Ht]. split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HK by lia. exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). rewrite HK by lia. exact (Ht x Hx).
Qed.
Lemma pb3_same_addr : forall (rd rd' : reader) q n, (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HK (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split.
- intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HK; [exact Hs|].
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 63) ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF. lia.
- intros Hn s Hs. rewrite HK; [exact (H4 Hn s Hs)|].
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  lia.
Qed.
Lemma pb3_same_lit : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} segs B (rd rd' : reader) a s,
  (forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) -> sa_lit segs B rd a s -> in_img segs a ->
  (forall x, in_img segs x -> 0 <= x < 2 ^ 47) -> sa_lit segs B rd' a s.
Proof.
intros rc SK segs B rd rd' a s HK (Ha & Hs & Hp & Hr & Hi) _ Hlo. split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
destruct (Hi (a + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof (Hlo _ He). apply (pb3_same_str rd rd' a s HK); [lia | lia | exact Hs].
Qed.


Lemma pb3_m32_16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 32) with ((2 * q) * 16) by lia. apply Z_mod_mult. Qed.
Lemma pb3_in_firstn : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.
Ltac pb3_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac pb3_ro_awr := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* ---------- the seed at FRAME (0x88074) ---------- *)
(* every register its own atom; atom 32 = c (Ereg's extra list); the region: slot 0xc8 of s1, read-only, holding c *)
Definition pb3_r1 : YP09.region := YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0xc8 0xc8 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition pb3_ss1s : sstate := mkSS (AF_reac_segconf_parse_file + 0x23c) sr_atoms [pb3_r1] None
  (mkFacts [(32%nat, mkAF 16 (2 ^ 64 - 16) 4); (19%nat, mkAF 1 (2 ^ 64 - 1) 0)] [] []).
Definition pb3_ss1n0 : sstate := mkSS (AF_reac_segconf_parse_file + 0x23c) sr_atoms [pb3_r1] None
  (mkFacts [(32%nat, mkAF 16 (2 ^ 64 - 16) 4)] [] []).
Definition pb3_ss1n : sstate := mkSS (AF_reac_segconf_parse_file + 0x23c) (sr_set sr_atoms (Z_to_bv 5 19) (SLit 0))
  [pb3_r1] None (mkFacts [(32%nat, mkAF 16 (2 ^ 64 - 16) 4)] [] []).
(* the argument word a3 of the snprintf: the label, or .str.1 *)
Definition pb3_w (lab : option (list Z)) (lp : Z) : Z := match lab with Some _ => lp | None => seg_litA_rc S_base end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* pf_pieces.v's hypotheses for B3's snprintf, and the listing's object atoms (B's SegObj) *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma pb3_obj35 : forall E, img_env VAL A_LIM E -> ew E 276%nat = w64 (seg_litA_rc F_s).
Proof.
intros E HE. rewrite (img_env_atomP E 276%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 276%nat with (A_OBJ 35). rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma pb3_obj34 : forall E, img_env VAL A_LIM E -> ew E 275%nat = w64 (seg_litA_rc S_base).
Proof.
intros E HE. rewrite (img_env_atomP E 275%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 275%nat with (A_OBJ 34). rewrite (OBJ 34%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.

Lemma pb3_seed1 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 c,
  getr rX (Z_to_bv 5 9) = w64 s1 -> 0 <= s1 -> s1 + 0xd0 <= 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0xc8) = Some c -> 16 <= c <= 2 ^ 64 - 16 -> c mod 16 = 0 ->
  (forall lp, getr rX (Z_to_bv 5 19) = w64 lp -> 1 <= lp < 2 ^ 64 ->
     st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 c])) pb3_ss1s
       (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x23c))) memc (seg_rom SEGS)))) /\
  (getr rX (Z_to_bv 5 19) = w64 0 ->
     st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 c])) pb3_ss1n
       (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x23c))) memc (seg_rom SEGS)))).
Proof.
intros Wc rX memc s1 c R9 H0 H1 Hw Hc1 Hc2.
set (E := Eimg (Ereg rX [w64 c])).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (RG : region_ok SEGS E (mrestrict (w_H Wc) memc) pb3_r1).
{ unfold region_ok, pb3_r1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|constructor].
  apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0xc8 8 (SOff 32 0) c).
  - rewrite pb3_den_atom0, E32. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact Hw. }
assert (HS0 : forall G, facts_ok E G -> st_ok_pi SEGS VAL E (mkSS (AF_reac_segconf_parse_file + 0x23c) sr_atoms [pb3_r1] None G)
  (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x23c))) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ intros G HG. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [exact RG | apply Forall_nil].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (F32 : afact_ok E 32 (mkAF 16 (2 ^ 64 - 16) 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. change (2 ^ 4) with 16. lia. }
split.
- intros lp R19 Hlp. rewrite restrict_mkst_fx. apply HS0.
  assert (U19 : bv_unsigned (ew E 19) = lp)
    by (subst E; rewrite (ew_Eimg_Ereg_nat rX _ 19 (Z_to_bv 5 19) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
  split; [|split; exact I].
  cbn [f_atoms atoms_ok]. split; [exact F32|]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, Z.pow_0_r, Z.mod_1_r. lia.
- intros R19. rewrite restrict_mkst_fx.
  assert (HSn : st_ok_pi SEGS VAL E pb3_ss1n0
    (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x23c))) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
  { apply HS0. split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [exact F32 | exact I]. }
  exact (st_ok_pi_pin_reg' E _ _ (Z_to_bv 5 19) 0 HSn R19 eq_refl).
Qed.

(* a register of the state after a run: its symbolic value is an atom of the seed (a register of rX or the extra atom
   32 = c, plus an offset), a literal, or a listing object atom *)
Ltac pb3_regq HS EE E32 HEI RG1 RG2 :=
  lazymatch goal with |- getr (ms_regs ?ms) (Z_to_bv 5 ?k) = _ =>
    let Rk := fresh "Rk" in prreg HS (Z_to_bv 5 k) Rk; rewrite Rk; clear Rk end;
  first
  [ exact (pb3_obj35 _ HEI) | exact (pb3_obj34 _ HEI)
  | reflexivity
  | rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; f_equal; unfold seg_spec.RC_READING, seg_spec.RC_GEN; lia
  | lazymatch goal with |- ew _ ?n = _ => let z := eval cbv in (Z.of_nat n) in rewrite (EE n (Z_to_bv 5 z) eq_refl) end;
    first [apply (pb3_rg _ _ _ _ RG1); solve [pb3_in] | apply (pb3_rg _ _ _ _ RG2); solve [pb3_in]] ].

(* ---------- the run FRAME (0x88074) -> the snprintf call (0x880cc) ---------- *)
Lemma pb3_run1 : forall v pos lyc Sc Wc rX memc mdc (Q : world SEGS -> config -> Prop),
  INV_FRAME B v pos lyc Sc Wc rX memc mdc ->
  (forall regsT memT mdT,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
     pf_rg regsT ([(10, p_c v + seg_spec.RC_READING); (11, 96); (12, seg_litA_rc F_s); (13, pb3_w (p_lab v) (p_lp v))] ++
       PB3_FI B v ++ [(21, pf_SH v pos); (22, p_c v + seg_spec.RC_GEN); (23, p_c v + seg_spec.RC_READING);
       (27, p_t v)]) ->
     getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298)) ->
     SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FRAME) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc rX memc mdc Q HI Kc.
pose proof HI as (HCX & HFI & HOBJ & HLAB & HRC & HSL & HFSH & HRG).
pose proof HOBJ as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
destruct (pb3_geo B v pos lyc Sc Wc rX memc mdc HCX HFI O5) as (G & Hin & EF & Hfrs & HAR & Hly & HFP & HSHP).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & HSL0 & HRG0).
pose proof HTF as (Hc0 & Hc16 & _).
pose proof HCX as (_ & _ & _ & Hc64 & _ & Ht64 & _ & Hl64 & _).
pose proof G as (S1 & S2 & S3 & S4 & S5 & _ & _ & _ & _ & _ & C1 & C2 & _).
pose proof O4 as (_ & Hc63 & _).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb3_rg rX _ 9 _ HRG0); pb3_in).
assert (Hw : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)) by exact (pb3_sl_get _ _ _ 0xc8 _ HSL0 ltac:(pb3_in)).
destruct (pb3_seed1 Wc rX memc (pf_s1 v) (p_c v) R9 ltac:(lia) ltac:(lia) Hw
  ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) Hc16) as [SDs SDn].
unfold cfg_at. change (w64 (BASE + PF_FRAME)) with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x23c))).
assert (HL0 : match p_lab v with Some _ => p_lp v <> 0 | None => p_lp v = 0 end)
  by (destruct HLAB as (HO & _); destruct (p_lab v); [exact (proj1 HO) | exact HO]).
destruct (p_lab v) as [l|] eqn:El.
- pose proof (SDs (p_lp v) ltac:(apply (pb3_rg rX _ 19 _ HRG); pb3_in) ltac:(lia)) as HS.
  set (E0 := Eimg (Ereg rX [w64 (p_c v)])) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr rX r)
    by (intros n r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E32 : ew E0 32 = w64 (p_c v)) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
  clearbody E0.
  assert (SHOK : sh_ok SEGS (SOff 20 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { pb3_ro_awr. }
  pb3_clear_md.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
    destruct Hin'. }
  assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298)))
    by (prreg HS (Z_to_bv 5 1) R1; rewrite R1; reflexivity).
  assert (QR : pf_rg (ms_regs ms) ([(10, p_c v + seg_spec.RC_READING); (11, 96); (12, seg_litA_rc F_s);
    (13, pb3_w (Some l) (p_lp v))] ++ PB3_FI B v ++ [(21, pf_SH v pos); (22, p_c v + seg_spec.RC_GEN);
    (23, p_c v + seg_spec.RC_READING); (27, p_t v)])).
  { unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      pb3_regq HS EE E32 HEI HRG0 HRG. }
  pmkst HS.
  exact (Kc _ _ _ HJ KM QR Q1).
- pose proof (SDn ltac:(rewrite <- HL0; apply (pb3_rg rX _ 19 _ HRG); pb3_in)) as HS.
  set (E0 := Eimg (Ereg rX [w64 (p_c v)])) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr rX r)
    by (intros n r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E32 : ew E0 32 = w64 (p_c v)) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
  clearbody E0.
  assert (SHOK : sh_ok SEGS (SOff 20 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { pb3_ro_awr. }
  pb3_clear_md.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
    repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
    destruct Hin'. }
  assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298)))
    by (prreg HS (Z_to_bv 5 1) R1; rewrite R1; reflexivity).
  assert (QR : pf_rg (ms_regs ms) ([(10, p_c v + seg_spec.RC_READING); (11, 96); (12, seg_litA_rc F_s);
    (13, pb3_w None (p_lp v))] ++ PB3_FI B v ++ [(21, pf_SH v pos); (22, p_c v + seg_spec.RC_GEN);
    (23, p_c v + seg_spec.RC_READING); (27, p_t v)])).
  { unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      pb3_regq HS EE E32 HEI HRG0 HRG. }
  pmkst HS.
  exact (Kc _ _ _ HJ KM QR Q1).
Qed.

(* ---------- the label at the call (pb3_w, pb3_T) ---------- *)
Lemma pb3_place_bound : forall ly S (W : world SEGS) mem md lp n,
  AR SEGS B ly S W mem md -> 0 <= n ->
  (sa_heap B ly S lp (n + 1) \/ sa_fframe ly S lp (n + 1) \/ sa_img SEGS B lp (n + 1)) ->
  lp + n + 1 <= alloc_ceiling.
Proof.
intros ly S W mem md lp n HAR Hn [(b & m & Hb & H1 & H2) | [(cid & p & Hin & Hc & H1 & H2) | Hi]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & _ & Hce & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid p HAR Hin) as (_ & Hfc & _). lia.
- destruct (Hi (lp + n) ltac:(lia)) as (Hi2 & _). pose proof (pa_img_range _ Hi2) as Hr.
  pose proof asan_consts as (A1 & _). unfold kImgEnd in Hr. lia.
Qed.
Lemma pb3_cspan : forall w (T : list Z), Z.of_nat (length T) + 1 <= seg_spec.cstr_span w T <= Z.of_nat (length T) + 8.
Proof.
intros w T. unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length T) + 1)) 8 ltac:(lia)). lia.
Qed.
Lemma pb3_snlen : forall T : list Z, sn_len (96 - 1) T = Z.of_nat (S (length (firstn 95 T))) /\
  sn_bytes (96 - 1) T = firstn 95 T ++ [0] /\ (length (firstn 95 T) < 96)%nat.
Proof.
intros T. unfold sn_len, sn_bytes. change (Z.to_nat (96 - 1)) with 95%nat.
rewrite length_app, length_firstn. cbn [length]. split; [lia|]. split; [reflexivity | lia].
Qed.
Lemma pb3_lab_call : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc memT mdT,
  INV_FRAME B v pos lyc Sc Wc rX memc mdc -> AR SEGS B lyc Sc Wc memT mdT ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
  pf_obj B v lyc Sc (rdW Wc memT) ->
  0 < pb3_w (p_lab v) (p_lp v) /\ Z.of_nat (length (pb3_T (p_lab v))) <= 65535 /\
  sa_str (rdW Wc memT) (pb3_w (p_lab v) (p_lp v)) (pb3_T (p_lab v)) /\
  sa_addr (rdW Wc memT) (pb3_w (p_lab v) (p_lp v)) (Z.of_nat (length (pb3_T (p_lab v))) + 1) /\
  amem_range (pb3_w (p_lab v) (p_lp v)) (Z.of_nat (length (pb3_T (p_lab v))) + 8) /\
  pb3_w (p_lab v) (p_lp v) + Z.of_nat (length (pb3_T (p_lab v))) + 1 <= alloc_ceiling /\
  sa_disj (pb3_w (p_lab v) (p_lp v)) (seg_spec.cstr_span (pb3_w (p_lab v) (p_lp v)) (pb3_T (p_lab v)))
    (p_c v + seg_spec.RC_READING) 96.
Proof.
intros v pos lyc Sc Wc rX memc mdc memT mdT HI HART KMT HOBJT.
pose proof HI as (HCX & HFI & HOBJ & HLAB & _).
pose proof (pb3_lab_amem B v HCX) as HAM.
pose proof HCX as (HPRE & _ & _ & _ & _ & _ & _ & Hl64 & (fe & (_ & _ & HL)) & _).
destruct (pb3_geo B v pos lyc Sc Wc rX memc mdc HCX HFI (proj1 (proj2 (proj2 (proj2 (proj2 HOBJ))))))
  as (G & _).
pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & C2 & _ & C4 & _).
pose proof HOBJT as (_ & _ & _ & _ & _ & _ & HLIT & _).
pose proof asan_consts as (A1 & _).
unfold pb3_w, pb3_T.
destruct HLAB as (HOS & HLB).
destruct (p_lab v) as [l|].
- destruct HOS as (Hlp0 & HSTR). destruct HLB as (_ & HADR).
  destruct HL as (Hl65 & Hplace & _ & Hdj).
  pose proof (pb3_place_bound (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) (p_lp v) (Z.of_nat (length l))
    (proj1 HPRE) ltac:(lia) ltac:(destruct Hplace as [H | [H | (H & _)]]; [left | right; left | right; right]; exact H)) as Hb.
  split; [lia|]. split; [apply Nat2Z.inj_le in Hl65; exact Hl65|].
  split; [apply (pb3_same_str _ _ _ _ KMT); [lia | lia | exact HSTR]|].
  split; [exact (pb3_same_addr _ _ _ _ KMT HADR)|].
  split; [exact HAM|]. split; [exact Hb | exact Hdj].
- assert (LB : sa_lit SEGS B (rdW Wc memT) (seg_litA_rc S_base) S_base).
  { apply HLIT. unfold PARSE_FILE_LITS. apply in_or_app. left. right. left. reflexivity. }
  destruct LB as (Ha0 & Hs & Hp & _ & Hi).
  assert (EL : Z.of_nat (length S_base) = 12) by (vm_compute; reflexivity).
  pose proof seg_litA_rc_S_base as ES.
  split; [lia|]. split; [rewrite EL; lia|].
  split; [exact Hs|]. split; [exact (Hp lyc Sc Wc memT mdT HART)|].
  rewrite EL, ES. unfold off_img, seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *.
  split; [unfold amem_range, kLowMemEnd; left; lia|]. split; [lia|].
  unfold sa_disj, seg_spec.cstr_span. rewrite ?EL, ?ES. change ((- (136032 + 12 + 1)) mod 8) with 3. lia.
Qed.

(* ---------- the snprintf at 0x880cc and the state after it (MID1, 0x880d0) ---------- *)
Ltac pb3_getq QR k := apply (pb3_bvr _ _ k); [reflexivity | apply (pb3_rg _ _ _ _ QR); solve [pb3_in]].
Lemma pb3_call1 : forall v pos lyc Sc Wc rX memc mdc (Q : world SEGS -> config -> Prop) regsT memT mdT,
  INV_FRAME B v pos lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memT a = rdW Wc memc a) ->
  pf_rg regsT ([(10, p_c v + seg_spec.RC_READING); (11, 96); (12, seg_litA_rc F_s); (13, pb3_w (p_lab v) (p_lp v))] ++
    PB3_FI B v ++ [(21, pf_SH v pos); (22, p_c v + seg_spec.RC_GEN); (23, p_c v + seg_spec.RC_READING); (27, p_t v)]) ->
  getr regsT (Z_to_bv 5 1) = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298)) ->
  (forall (fx1 : YK11.FPState) rX1 memc1 mdc1, fxrel fx fx1 -> frm0 fx1 ->
     pb3_MID1 B v pos lyc Sc Wc memc rX1 memc1 mdc1 ->
     SRr SEGS Wc (@cfg_at fx1 SEGS (BASE + (AF_reac_segconf_parse_file + 0x298)) rX1 memc1 mdc1) Q) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT) Q.
Proof.
intros v pos lyc Sc Wc rX memc mdc Q regsT memT mdT HI HJT KMT QR Q1 Kc.
pose proof HI as (HCX & HFI & HOBJ & HLAB & HRC & HSL & HFSH & HRG).
pose proof HOBJ as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
destruct (pb3_geo B v pos lyc Sc Wc rX memc mdc HCX HFI O5) as (G & Hin & EF & Hfrs & HAR & Hly & HFP & HSHP).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & HTF & HSL0 & HRG0).
pose proof HCX as (_ & _ & _ & Hc64 & _ & Ht64 & _ & Hl64 & _).
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
pose proof O4 as (_ & Hc63 & Hcam & _).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in S1.
pose proof pf_B_values as (_ & _ & _ & Egw & Egd & _ & _ & _ & _ & _ & EFs).
pose proof (pb3_SHb v pos G) as (ESH & SH1 & SH2 & _ & _).
pose proof HJT as (HART & _).
pose proof O5 as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrq].
(* the cut's objects at the call's reader: the run wrote nothing *)
assert (KT : pb3_kept v pos (rdW Wc memc) (rdW Wc memT)).
{ split; [intros a Ha _; exact (KMT a Ha) | intros a Ha Hv; rewrite (KMT a Ha); exact Hv]. }
assert (HOBJT : pf_obj B v lyc Sc (rdW Wc memT)).
{ apply (pb3_keep_obj B v pos lyc Sc Wc memc mdc (rdW Wc memc)); try assumption.
  destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTD & _) & _)) & _).
  exact HTD. }
pose proof HOBJT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
destruct (pb3_lab_call v pos lyc Sc Wc rX memc mdc memT mdT HI HART KMT HOBJT)
  as (Lw0 & Ll65 & Lstr & Laddr & Lam & Lbd & Ldj).
remember (pb3_w (p_lab v) (p_lp v)) as w eqn:Ew. remember (pb3_T (p_lab v)) as T eqn:ET.
pose proof (pb3_snlen T) as (SNL & SNB & SNT).
pose proof (pb3_cspan w T) as CSP.
assert (Q10 : getr regsT 10 = w64 (p_c v + seg_spec.RC_READING)) by pb3_getq QR 10.
assert (Q11 : getr regsT 11 = w64 96) by pb3_getq QR 11.
assert (Q12 : getr regsT 12 = w64 (seg_litA_rc F_s)) by pb3_getq QR 12.
assert (Q2 : getr regsT 2 = w64 (pf_s1 v)) by pb3_getq QR 2.
assert (Q3 : getr regsT 3 = w64 (as_gp B)) by pb3_getq QR 3.
assert (Q4 : getr regsT 4 = w64 (as_tp B)) by pb3_getq QR 4.
assert (Q1' : getr regsT 1 = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298)))
  by (apply (pb3_bvr _ _ 1); [reflexivity | exact Q1]).
assert (Hsp : spZ regsT = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (FMT : sa_lit SEGS B (rdW Wc memT) (seg_litA_rc F_s) F_s)
  by (apply T7; unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity).
eapply SRr_bind.
{ apply (b3t_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (pa_sigma SS___interceptor_trampoline_snprintf)
    (ASNPRINTF fx) Wc regsT memT STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v)
    (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdT 0 (p_c v + seg_spec.RC_READING) 96 (seg_litA_rc F_s) T
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298))) HJT Q10 Q11 Q12).
  - lia.
  - unfold seg_spec.RC_READING. lia.
  - unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
  - exact Hsp.
  - apply pb3_m16; [exact (pb3_m32_16 _ S5) | exact S3].
  - lia.
  - unfold CMD_SNP_K, ESTACK. rewrite ESTK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1'.
  - apply ret_ok_codeptr_v; [unfold AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split.
    + right; left. split.
      * exists (p_c v + seg_spec.RC_READING, p_c v + seg_spec.RC_GEN + 4).
        split; [unfold seg_spec.RC_PARSE_W; right; right; left; reflexivity|].
        cbn [fst snd]. unfold seg_spec.RC_READING, seg_spec.RC_GEN in *. lia.
      * exists bc, mc. split; [exact Hbc|]. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
    + unfold CMD_SNP_K, ESTACK. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
  - intros a Ha _ [[_ Hi] | Hs]; exfalso.
    + pose proof (pa_img_range a Hi) as Hr. unfold off_img, kImgEnd, seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
    + unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
  - unfold amem_range in *. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
  - pose proof T4 as (_ & _ & _ & HRA & _).
    apply (range_addressable_sub _ _ _ _ _ _ HRA); unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE; lia.
  - pose proof T4 as (_ & _ & _ & _ & HHV).
    apply (pb3_hull_sub _ _ _ _ _ (HHV ltac:(unfold seg_spec.SEG_C_SIZE; lia)));
      unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE; lia.
  - rewrite SNL. unfold off_img in *. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
  - unfold CMD_IMG_HI, CMD_SNP_K, ESTACK, kImgEnd. lia.
  - exact T9.
  - rewrite Egw. lia.
  - rewrite Egw. unfold CMD_IMG_HI, kImgEnd. lia.
  - rewrite Egd. lia.
  - rewrite Egd. unfold CMD_IMG_HI, kImgEnd. lia.
  - rewrite Egw. unfold CMD_IMG_LO. lia.
  - rewrite Egd. unfold CMD_IMG_LO. lia.
  - apply (b3t_FR_s_regs (rdW Wc memT) _ (seg_litA_rc F_s) w T regsT).
    + unfold argZ. change (10 + 3) with 13. rewrite (pb3_rg _ _ 13 _ QR ltac:(pb3_in)). unfold w64.
      apply unsigned_lit_small. lia.
    + rewrite EFs. lia.
    + rewrite EFs. unfold CMD_IMG_LO. lia.
    + rewrite EFs. unfold CMD_GOTW. lia.
    + exact (proj1 (proj2 FMT)).
    + pose proof FMT as (_ & _ & Hp & _). pose proof (Hp lyc Sc Wc memT mdT HART) as Hpa.
      rewrite b3t_F_s_len in Hpa. exact Hpa.
    + rewrite Hsp, SNL, EFs. unfold snp_out.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint; cbn [fst snd].
      unfold off_img, seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
    + exact Lw0.
    + exact (b3t_bytes_range_aview SEGS (w_H Wc) memT w T Lstr).
    + lia.
    + exact Lstr.
    + exact Laddr.
    + exact Lam.
    + rewrite Hsp, SNL. unfold snp_out.
      apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia|].
      apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint; cbn [fst snd]. unfold sa_disj in Ldj. lia.
  - lia.
  - intros a (sg & Hsg & Hw & Hr) Ho He. exact (T8 a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
  - exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & _ & Hby & Hkp & Hpr & _).
change (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298))) mem2 (seg_rom SEGS)) md2)
  with (@cfg_at fx1 SEGS (BASE + (AF_reac_segconf_parse_file + 0x298)) regs2 mem2 md2).
apply (Kc fx1 regs2 mem2 md2 Hfx (fxrel_frm0 fx fx1 HFRM Hfx)).
rewrite SNL in Hby, Hkp. rewrite SNB in Hby.
(* every byte outside the destination prefix and the call's window is the cut's *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (p_c v + seg_spec.RC_READING <= a < p_c v + seg_spec.RC_READING + Z.of_nat (S (length (firstn 95 T)))) ->
    ~ (pf_s1 v - CMD_SNP_K <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha H1 H2. rewrite (Hkp a Ha H1) by (intros H3; apply H2; lia). exact (KMT a Ha). }
assert (Hsnk : CMD_SNP_K = 8192) by reflexivity.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
split; [exact HJ2|].
split.
{ split.
  - intros a Ha Hn. apply K2; [exact Ha | | ]; intros Hq; apply Hn; unfold pb3_Wr; rewrite ?ESTK;
      [right; left; unfold seg_spec.RC_READING, seg_spec.RC_GEN in *; lia | left; rewrite Hsnk in Hq; lia].
  - intros a Ha Hv.
    destruct (Z_lt_le_dec a (p_c v + seg_spec.RC_READING)) as [L1 | L1];
    [|destruct (Z_lt_le_dec a (p_c v + seg_spec.RC_READING + Z.of_nat (S (length (firstn 95 T))))) as [L2 | L2]].
    + destruct (Z_lt_le_dec a (pf_s1 v - CMD_SNP_K)) as [L3 | L3]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L4 | L4]].
      * rewrite K2 by lia. exact Hv.
      * apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ESTK. lia.
      * rewrite K2 by lia. exact Hv.
    + replace a with (p_c v + seg_spec.RC_READING + (a - (p_c v + seg_spec.RC_READING))) by lia.
      rewrite Hby by lia. discriminate.
    + destruct (Z_lt_le_dec a (pf_s1 v - CMD_SNP_K)) as [L3 | L3]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L4 | L4]].
      * rewrite K2 by lia. exact Hv.
      * apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ESTK. lia.
      * rewrite K2 by lia. exact Hv. }
split.
{ unfold pb3_rc1. rewrite <- ET.
  apply (b3f_rconf_reading (rdW Wc memc) (rdW Wc mem2) (p_c v) (p_rcs v) (firstn 95 T) HRC SNT).
  - intros Hin0. apply pb3_in_firstn in Hin0. destruct Lstr as ((_ & Hn0) & _). exact (Hn0 Hin0).
  - pose proof (b3t_bytes_range_aview SEGS (w_H Wc) memT w T Lstr) as BR.
    apply Forall_forall. intros x Hx. apply pb3_in_firstn in Hx. rewrite Forall_forall in BR. pose proof (BR x Hx). lia.
  - intros i Hi. exact (Hby i Hi).
  - intros a Ha Hn. apply K2; [lia | exact Hn |].
    unfold seg_spec.SEG_C_SIZE, CMD_SNP_K, ESTACK in *. lia. }
split.
{ assert (KS : forall a, pf_s1 v <= a < pf_s1 v + 0xe0 -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha. apply K2; [lia | | lia]. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia. }
  unfold pf_sl. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  (rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem2)); [| intros k Hk; apply KS; lia]);
  first [apply (pb3_sl_get _ _ _ _ _ HSL); solve [pb3_in] | apply (pb3_sl_get _ _ _ _ _ HSL0); solve [pb3_in]]. }
split.
{ intros i Hi. rewrite K2; [exact (HFSH i Hi) | unfold kLowMemEnd, kHighShadowEnd in *; lia | |].
  - unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *. lia.
  - unfold CMD_SNP_K, ESTACK, kLowMemEnd, kHighShadowEnd in *. lia. }
unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  rewrite HP2 by (unfold acallee_saved; lia); apply (pb3_rg _ _ _ _ QR); solve [pb3_in].
Qed.

(* ---------- the piece: FRAME -> MID1 ---------- *)
Lemma pb3_s1 : forall v pos lyc Sc Wc rX memc mdc (Q : world SEGS -> config -> Prop),
  INV_FRAME B v pos lyc Sc Wc rX memc mdc ->
  (forall (fx1 : YK11.FPState) rX1 memc1 mdc1, fxrel fx fx1 -> frm0 fx1 ->
     pb3_MID1 B v pos lyc Sc Wc memc rX1 memc1 mdc1 ->
     SRr SEGS Wc (@cfg_at fx1 SEGS (BASE + (AF_reac_segconf_parse_file + 0x298)) rX1 memc1 mdc1) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_FRAME) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc rX memc mdc Q HI Kc.
apply (pb3_run1 v pos lyc Sc Wc rX memc mdc Q HI).
intros regsT memT mdT HJT KMT QR Q1.
exact (pb3_call1 v pos lyc Sc Wc rX memc mdc Q regsT memT mdT HI HJT KMT QR Q1 Kc).
Qed.

End x.
End d.
