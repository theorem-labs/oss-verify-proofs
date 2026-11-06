(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 1355 of its 1430 lines of code are new or changed and 3265 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacPortsParse.v; 1202 of its 1364 lines of code are new or changed and 1268 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC4b YC1h YC1g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require RcLeafLib.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_PORTS_PARSE_STK : Z := 16 + ESTACK.
Definition treac_ports_parse_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p q : Z) (bs : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst (fx := fq) regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    getr regs2 10 = w64 (if ports_ok p q bs then 0 else -1) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs) ->
       ~ (q <= a < q + 12) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ (q <= b + i < q + 12) ->
       aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
    (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall cid pos a, In (cid, pos) (frames Sc) ->
       (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
       ~ (q <= a < q + 12) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
    (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs) ->
       apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
    (forall a, spZ regs - REAC_PORTS_PARSE_STK <= a < spZ regs -> apresent (w_H W2) mem2 a) /\
    (if ports_ok p q bs
     then val_mem SEGS (mrestrict (w_H W2) mem2) q 4 (4 * n_in bs) /\
          val_mem SEGS (mrestrict (w_H W2) mem2) (q + 4) 4 (4 * n_out bs) /\
          val_mem SEGS (mrestrict (w_H W2) mem2) (q + 8) 4 (16 * bt bs 7)
     else forall a, q <= a < q + 12 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
Definition treac_ports_parse_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (p q : Z) (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  q + 12 <= 2 ^ 63 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (p <> 0 -> q <> 0 ->
     length bs = 20%nat /\ p + 20 <= 2 ^ 47 /\ off_img p 20 /\
     (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) /\
     (spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20 /\
     (forall a, p <= a < p + 20 -> apresent (w_H W) memc a) /\
     garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs) /\
     q mod 4 = 0 /\ (q + 12 <= p \/ p + 20 <= q) /\
     (q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 12 /\
     (forall a, q <= a < q + 12 ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Import YP0m YP0l YCbn YP0e YP06 YP03 YA0o YA0q YC4b YC1h YC1g YC44.
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Definition RP_SB : Z := 0x7fff8000.
Definition RP_Bx : sv := SOff 32 0.
Definition RP_Bx0 : sv := SLit RP_SB.
Definition RP_Bspan : Z * Z := (RP_SB, RP_SB + 2 ^ 44 - 1).
Definition rp_preg : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 4 (CVal 1 (SOff 35 0));
   YP09.mkChunk 7 (CVal 1 (SOff 36 0))].
Definition rp_qreg : YP09.region := YP09.mkRegion (Some 11%nat) 0 12 0 12 [].
Definition rp_facts : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 1 (2 ^ 47 - 20) 0); (11%nat, mkAF 4 (2 ^ 47 - 12) 2);
   (32%nat, mkAF RP_SB RP_SB 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
   (36%nat, mkAF 0 255 0)] [] [].
Definition ss_rp : sstate :=
  mkSS AF_both3_reac_ports_parse sr_atoms [stack_region 16; got_regionP; bcell_regionP 32; rp_preg] None rp_facts.
Definition ss_rp0 : sstate :=
  mkSS AF_both3_reac_ports_parse sr_atoms [stack_region 16] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition rp_SHp : list shent := [mkSHE 10 0 20].
Definition rp_SH : list shent := [mkSHE 10 0 20; mkSHE 11 0 12].
Definition rp_extra (bs : list byte) : list word :=
  [Z_to_bv 64 RP_SB; Z_to_bv 64 (bt bs 0); Z_to_bv 64 (bt bs 1); Z_to_bv 64 (bt bs 4); Z_to_bv 64 (bt bs 7)].
Definition ss_rpLH : sstate := mkSS 0x8778
  [SLit 0; SOff 1 0; SOff 2 (-16); SOff 3 0; SOff 4 0; SLit 2; SOff 10 8; SLit 1; SOff 8 0; SOff 9 0; SOff 10 0;
   SOff 11 0; SOff 10 8; SLit 0; SOff 32 0; SLit 0; SOff 10 8; SLit 12; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0;
   SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
  [YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]; got_regionP; bcell_regionP 32;
   rp_preg] None rp_facts.
Definition rp_regsL : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 5%bv (SLit 2)) 7%bv (SLit 1)) 12%bv (SOff 16 0)) 6%bv (SOff 16 0))
    14%bv (SOff 32 0).
Definition rp_bytL : YP09.region := YP09.mkRegion (Some 16%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition rp_factsL : facts := mkFacts
  [(13%nat, mkAF 0 11 0); (15%nat, mkAF 0 11 0); (16%nat, mkAF 9 (2 ^ 47 - 1) 0); (17%nat, mkAF 1 12 0);
   (32%nat, mkAF RP_SB RP_SB 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_rpL : sstate := mkSS 0x8778 rp_regsL [got_regionP; bcell_regionP 32; rp_bytL] None rp_factsL.
Definition rp_SHL : list shent := [mkSHE 16 0 1].
Definition rp_extraL (c : Z) : list word := [Z_to_bv 64 RP_SB; Z_to_bv 64 c].
Definition RP_CLOB : list (bv 5) := [5; 6; 7; 12; 13; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition RP_KEPT : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 11; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition rp_kept (W : world SEGS) (sp : Z) (memc m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).
Definition rp_keptQ (W : world SEGS) (sp q : Z) (memc m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 16 <= a < sp) -> ~ (q <= a < q + 12) ->
     aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) m a).
Lemma rp_den_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n c x Hn Hx Hxc. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff n c))). f_equal.
exact (U_atom_off E n x c Hn Hx Hxc).
Qed.
Lemma rp_den_sll2 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x <= 12 ->
  sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 2)) = Z_to_bv 64 (4 * x).
Proof.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n x Hn) by lia.
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma rp_den_sll4 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 256 ->
  sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 4)) = Z_to_bv 64 (16 * x).
Proof.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n x Hn) by lia.
change (Z.land (zcanon 4) 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma rp_U_c30 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x <= 12 ->
  U E (SAluw ALU_SRL (SOff n 536870912) (SLit 30)) = 0.
Proof.
intros E n x Hn Hx. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
rewrite U_SLit, (U_atom_off E n x 536870912 Hn) by lia.
change (zcanon 30 mod 2 ^ 32) with 30. change (Z.land 30 31) with 30.
rewrite (Z.mod_small (x + 536870912)) by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.div_small (x + 536870912)) by lia. reflexivity.
Qed.
Lemma rp_U_or4 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 256 ->
  U E (SAlu ALU_OR (SOff n 0) (SLit 4)) = Z.lor x 4.
Proof.
intros E n x Hn Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n x Hn) by lia.
change (zcanon 4) with 4.
pose proof (RcLeafLib.rcl_all256 (fun y => (0 <=? Z.lor y 4) && (Z.lor y 4 <? 256)) ltac:(vm_compute; reflexivity) x Hx) as Hb.
cbv beta in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma rp_lor4 : forall x, 0 <= x < 256 -> Z.lor x 4 = 132 -> x = 128 \/ x = 132.
Proof.
intros x Hx H.
pose proof (RcLeafLib.rcl_all256 (fun y => negb (Z.lor y 4 =? 132) || (y =? 128) || (y =? 132))
  ltac:(vm_compute; reflexivity) x Hx) as Hb.
cbv beta in Hb. rewrite H, Z.eqb_refl in Hb. cbn [negb orb] in Hb.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.eqb_eq in Hb; [left|right]; exact Hb.
Qed.
Lemma rp_byte : forall m p (bs : list byte) j, garr8 SEGS m p (map (fun b : byte => bv_unsigned b) bs) ->
  (j < length bs)%nat -> val_mem SEGS m (p + Z.of_nat j) 1 (bt bs j) /\ 0 <= bt bs j < 256.
Proof.
intros m p bs j HG Hj.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
destruct (HG j Hj') as [Hv Hr].
assert (E : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bt bs j).
{ rewrite (nth_indep _ 0 ((fun b : byte => bv_unsigned b) (Z_to_bv 8 0))) by exact Hj'. rewrite map_nth. reflexivity. }
rewrite E in Hv, Hr. split; assumption.
Qed.
Lemma rp_clob_cases : forall r : bv 5, reg_in r RP_CLOB = false -> r = 0%bv \/ In r RP_KEPT.
Proof.
intros r Hr. pose proof (YP01.all_regs_in r) as Hin. cbv [YP01.all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv [RP_KEPT In]; tauto] |]).
destruct Hin.
Qed.
Lemma rp_frame_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hro x. apply HF. intros (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ rs) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.
Lemma rp_aview_eq : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Heq. unfold aview, mbyte, mrestrict. cbv beta. rewrite Heq. reflexivity. Qed.
Lemma rp_apres_eq : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  apresent H m a -> apresent H m' a.
Proof. intros H m m' a Heq. unfold apresent. rewrite Heq. tauto. Qed.
Lemma rp_kept_step : forall (W : world SEGS) sp memc (m m' : word -> option byte) Ex rs,
  rp_kept W sp memc m ->
  frame_of Ex rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi -> sp - 16 <= a < sp) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  rp_kept W sp memc m'.
Proof.
intros W sp memc m m' Ex rs [K P] HF Hw HG. split.
- intros a Ha Hn. transitivity (aview SEGS (w_H W) m a); [|exact (K a Ha Hn)].
  exact (kept_of_frame Ex rs (w_H W) m m' (fun a => sp - 16 <= a < sp) HF Hw a Ha Hn).
- intros a Ha. exact (apresent_grows _ _ _ a HG (P a Ha)).
Qed.
Lemma rp_keptQ_step : forall (W : world SEGS) sp q memc (m m' : word -> option byte) Ex rs,
  rp_keptQ W sp q memc m ->
  frame_of Ex rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi ->
     (sp - 16 <= a < sp) \/ (q <= a < q + 12)) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  rp_keptQ W sp q memc m'.
Proof.
intros W sp q memc m m' Ex rs [K P] HF Hw HG. split.
- intros a Ha Hs Hq. transitivity (aview SEGS (w_H W) m a); [|exact (K a Ha Hs Hq)].
  apply (kept_of_frame Ex rs (w_H W) m m' (fun a => (sp - 16 <= a < sp) \/ (q <= a < q + 12)) HF Hw a Ha).
  intros [X|X]; [exact (Hs X) | exact (Hq X)].
- intros a Ha. exact (apresent_grows _ _ _ a HG (P a Ha)).
Qed.
Lemma rp_kept_eq : forall (W : world SEGS) sp memc (m m' : word -> option byte),
  rp_kept W sp memc m -> (forall x, m' x = m x) -> rp_kept W sp memc m'.
Proof.
intros W sp memc m m' [K P] Heq. split.
- intros a Ha Hn. rewrite (rp_aview_eq (w_H W) m m' a Heq). exact (K a Ha Hn).
- intros a Ha. exact (rp_apres_eq (w_H W) m m' a Heq (P a Ha)).
Qed.
Ltac rp_winS Usp :=
  lazymatch goal with |- forall b wlo whi a, In (b, wlo, whi) (windows ?rs) -> _ =>
  let w := eval vm_compute in (windows rs) in change (windows rs) with w;
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; cbn [In] in Hin;
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha; first [lia | rewrite Usp in Ha; lia] |]);
  destruct Hin end.
Ltac rp_winQ Usp Uq :=
  lazymatch goal with |- forall b wlo whi a, In (b, wlo, whi) (windows ?rs) -> _ =>
  let w := eval vm_compute in (windows rs) in change (windows rs) with w;
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; cbn [In] in Hin;
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha;
    first [lia | rewrite Usp in Ha; left; lia | rewrite Uq in Ha; right; lia] |]);
  destruct Hin end.
Ltac rp_keep Usp KC :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m) (mrestrict _ ?m'), HG : mem_grows _ _ |- _ =>
  lazymatch type of KC with rp_kept ?W ?sp ?memc _ =>
  let Hw := fresh "Hw" in let KC2 := fresh "KC" in
  assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi ->
     sp - 16 <= a < sp) by rp_winS Usp;
  pose proof (rp_kept_step W sp memc m m' Ex rs KC HFr Hw HG) as KC2;
  clear KC HFr HG Hw; try (match goal with H : frame_of _ _ _ _ |- _ => clear H end); rename KC2 into KC end end.
Ltac rp_keepQ Usp Uq KQ :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m) (mrestrict _ ?m'), HG : mem_grows _ _ |- _ =>
  lazymatch type of KQ with rp_keptQ ?W ?sp ?q ?memc _ =>
  let Hw := fresh "Hw" in let KQ2 := fresh "KQ" in
  assert (Hw : forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val Ex b + wlo <= a < base_val Ex b + whi ->
     (sp - 16 <= a < sp) \/ (q <= a < q + 12)) by rp_winQ Usp Uq;
  pose proof (rp_keptQ_step W sp q memc m m' Ex rs KQ HFr Hw HG) as KQ2;
  clear KQ HFr HG Hw; try (match goal with H : frame_of _ _ _ _ |- _ => clear H end); rename KQ2 into KQ end end.
Ltac rp_awr Usp spz sp0 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spz - sp0));
      [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | ] ].
Ltac rp_awrQ Usp spz sp0 q Uq Hwr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spz - sp0));
      [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | ]
    | eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 11 q);
      [reflexivity | exact Uq | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; apply Hwr; lia | ] ].
Ltac rp_awr0 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ].
Lemma rp_q_off : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k q,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
  (forall a, q <= a < q + 12 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  forall a, q <= a < q + 12 -> (a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a) /\ a < 2 ^ 47 /\ ~ in_img SEGS a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k q HJ Hz Hwr a Ha.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hwr a Ha))
  as (_ & [[Hc Hs] | [(_ & b & n & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]).
- split; [right; unfold YImgTop.IMG_TOP; lia|]. split; [lia|].
  intros Himg. pose proof (Hsegs a Himg). lia.
- pose proof (blk_off_imgP B _ _ _ _ _ b n HAR Hbin) as Ho. unfold off_img in Ho.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hbin) as (_ & Hb4096 & Hbceil & _).
  split; [lia|]. split; [lia|]. exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  pose proof (frm_off_imgP B _ _ _ _ _ cid pos HAR Hin') as Ho. unfold off_img in Ho.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin') as (Hf0 & Hfc & _).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. split; [lia|]. split; [lia|].
  exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr).
- exfalso. unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *. lia.
Qed.
Section w.
Context {fx : YK11.FPState}.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Lemma rp_post_build : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p q : Z) (bs : list byte) (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word) (pc : word) (Ex : Z -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  0 <= q -> q + 12 <= 2 ^ 63 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (forall a, Ex a -> q <= a < q + 12) ->
  (forall a, Ex a -> ~ in_img SEGS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> ~ Ex a ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  pc = getr regs 1 -> aregs_preserved regs regs2 ->
  getr regs2 10 = w64 (if ports_ok p q bs then 0 else -1) ->
  (if ports_ok p q bs
   then val_mem SEGS (mrestrict (w_H W) mem2) q 4 (4 * n_in bs) /\
        val_mem SEGS (mrestrict (w_H W) mem2) (q + 4) 4 (4 * n_out bs) /\
        val_mem SEGS (mrestrict (w_H W) mem2) (q + 8) 4 (16 * bt bs 7)
   else forall a, ~ Ex a) ->
  treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs W
    (mkCfg (mkst (fx := fx) regs2 pc mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs mem2 md2 regs2 pc Ex
  HJc HJ2 Hlo Hhi Hq0 Hq63 Hqw HEx HExI HK HP Hpc HRP H10 Hres.
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
pose proof HJc as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
unfold treac_ports_parse_post. exists lyc, Sc, regs2, mem2, md2.
split; [rewrite Hpc; reflexivity|]. split; [exact HJ2|]. split; [exact HRP|]. split; [reflexivity|].
split; [apply Permutation_refl|]. split; [exact H10|].
split; [intros a Ha Hw Hq; apply HK; [lia | lia | intros HE; exact (Hq (HEx a HE))]|].
split.
{ intros b m i Hb Hi Hq.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _).
  apply HK; [lia | lia | intros HE; exact (Hq (HEx _ HE))]. }
split.
{ intros a Himg Hown Herr. pose proof (Hsegs a Himg) as Hlow.
  apply HK; [lia | lia | intros HE; exact (HExI a HE Himg)]. }
split.
{ intros cid pos a Hf Hr Hq.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs0.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs0) as Hse.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  apply HK; [lia | lia | intros HE; exact (Hq (HEx a HE))]. }
split; [intros a Ha Hw Hp; exact (HP a Hp)|].
split; [intros a Ha; apply Hpres2; lia|].
destruct (ports_ok p q bs); [exact Hres|].
intros a Ha. apply HK; [lia | lia | exact (Hres a)].
Qed.
Lemma rp_entry0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_rp0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_ports_parse)) memc (seg_rom SEGS))) /\
  sh_ok SEGS RP_Bx0 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hslo Hshi. split; [|constructor].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold ss_rp0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.
Ltac rp_fail HS HJ HJc KC Hok Hra Hslo Hshi Hq0 Hq63 Hqsp E1 HAE Hsegs :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ssx (restrict _ ?msc) =>
  let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10;
  eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat := fresh "mat" in intros mat;
  apply (rp_post_build _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msc) _ (ms_regs msc) _ (fun _ => False) HJc
     ltac:(apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ) Hslo Hshi Hq0 Hq63 Hqsp);
  [ intros ? []
  | intros ? []
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in intros a Ha Hs _; exact (proj1 KC a Ha Hs)
  | exact (proj2 KC)
  | cbn [ms_regs]; rewrite Q1, E1; exact Hra
  | eapply (aregs_preserved_of_st_ok SEGS _ E _ _ _ _ HS); [exact HAE | vm_compute; reflexivity]
  | rewrite Hok; cbn [ms_regs]; rewrite Q10; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity
  | rewrite Hok; intros ? [] ] end.
Lemma rp_zero : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p q : Z) (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  q + 12 <= 2 ^ 63 -> (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (p = 0 \/ q = 0) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hra H10 H11 Hp Hq Hal16 Hslo Hshi
  Hq63 Hqsp Hpq.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
destruct (rp_entry0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hslo Hshi) as [HS SHOK].
pose proof HJ as HJc.
assert (WS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
assert (Hq0 : 0 <= q) by lia.
assert (Hok : ports_ok p q bs = false).
{ unfold ports_ok. destruct Hpq as [-> | ->]; [reflexivity|]. rewrite Z.eqb_refl. cbn [negb].
  rewrite andb_false_r. reflexivity. }
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (apply (EE 1%nat 1%bv); reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite (EE 10%nat 10%bv) by reflexivity; exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 q) by (rewrite (EE 11%nat 11%bv) by reflexivity; exact H11).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (KC : rp_kept W (spZ regs) memc memc) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_ports_parse)) with (Z_to_bv 64 (BASE + AF_both3_reac_ports_parse)).
paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|].
rp_keep Usp KC.
psrr_branch_tok RUN BR HS SHOK RP_Bspan.
- clear Hc. paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC.
  rp_fail HS HJ HJc KC Hok Hra Hslo Hshi Hq0 Hq63 Hqsp E1 HAE Hsegs.
- rewrite branch_eq_U, (U_atom E 10 p E10), U_lit in Hc by lia.
  assert (P0 : p <> 0) by (destruct (Z.eqb_spec p 0); [discriminate Hc | lia]). clear Hc.
  paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC.
  psrr_branch_tok RUN BR HS SHOK RP_Bspan.
  + clear Hc. paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC.
    rp_fail HS HJ HJc KC Hok Hra Hslo Hshi Hq0 Hq63 Hqsp E1 HAE Hsegs.
  + rewrite branch_eq_U, (U_atom E 11 q E11), U_lit in Hc by lia.
    exfalso. destruct (Z.eqb_spec q 0); [discriminate Hc | lia].
Qed.
Lemma rp_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    p q (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q -> 1 <= p -> p + 20 <= 2 ^ 47 -> 4 <= q -> q + 12 <= 2 ^ 47 ->
  q mod 4 = 0 -> (spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK) -> off_img p 20 ->
  (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) -> length bs = 20%nat ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20 ->
  garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (rp_extra bs))) ss_rp
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_ports_parse)) memc (seg_rom SEGS))) /\
  sh_ok SEGS RP_Bx rp_SHp (Eimg (Ereg regs (rp_extra bs))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hal16 Hslo Hshi H10 H11 Hp1 Hp47 Hq4
  Hq47 Hq4m Hpsp Hpoff Hpz LB Hrad HG.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as Q0. pose proof (pa_val_range (A_OBJ 12)) as Q12.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hpoff.
destruct (rp_byte _ p bs 0 HG ltac:(lia)) as [V0 B0].
destruct (rp_byte _ p bs 1 HG ltac:(lia)) as [V1 B1].
destruct (rp_byte _ p bs 4 HG ltac:(lia)) as [V4 B4].
destruct (rp_byte _ p bs 7 HG ltac:(lia)) as [V7 B7].
set (E := Eimg (Ereg regs (rp_extra bs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rp_extra bs)) n)
  by (intros n Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 RP_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bt bs 0)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bt bs 1)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bt bs 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (bt bs 7)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
split.
- rewrite restrict_mkst_fx. unfold ss_rp. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rp_preg, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) RP_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RP_SB; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    * rewrite (VB 10%nat p E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      -- apply (chunk_ok_val SEGS E _ p 0 1 (SOff 33 0) (bt bs 0));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact V0].
      -- apply (chunk_ok_val SEGS E _ p 1 1 (SOff 34 0) (bt bs 1));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact V1].
      -- apply (chunk_ok_val SEGS E _ p 4 1 (SOff 35 0) (bt bs 4));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact V4].
      -- apply (chunk_ok_val SEGS E _ p 7 1 (SOff 36 0) (bt bs 7));
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | exact V7].
  + apply pairwise_disjoint_of_extents. unfold rp_preg, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat p E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold RP_SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold RP_SB. repeat match goal with |- _ /\ _ => split end; first [exact Hal16 | exact Hq4m | exact I | lia].
- unfold sh_ok, rp_SHp. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E RP_Bx 10 p 20 p 0 20 Hrad).
  + unfold U, RP_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold RP_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rp_loop_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md kj (regs : bvmap 5 word)
    p (bs : list byte) (k : nat),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj ->
  (k < 12)%nat -> length bs = 20%nat -> 1 <= p -> p + 20 <= 2 ^ 47 -> off_img p 20 ->
  (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 20 ->
  garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) bs) ->
  getr regs 5 = w64 2 -> getr regs 6 = w64 (p + 8 + Z.of_nat k) -> getr regs 7 = w64 1 ->
  getr regs 12 = w64 (p + 8 + Z.of_nat k) -> getr regs 13 = w64 (cnt is_out bs k) -> getr regs 14 = w64 RP_SB ->
  getr regs 15 = w64 (cnt is_in bs k) -> getr regs 16 = w64 (p + 8 + Z.of_nat k) -> getr regs 17 = w64 (12 - Z.of_nat k) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (rp_extraL (bt bs (8 + k))))) ss_rpL
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x8778)) mem (seg_rom SEGS))) /\
  sh_ok SEGS RP_Bx rp_SHL (Eimg (Ereg regs (rp_extraL (bt bs (8 + k))))) (mrestrict (w_H W) mem).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj regs p bs k HJ Hk LB Hp1 Hp47 Hpoff Hpz Hrad HG
  G5 G6 G7 G12 G13 G14 G15 G16 G17.
pose proof HJ as (HAR & _).
destruct (al_const _ _ LAWS lyc Sc W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as Q0. pose proof (pa_val_range (A_OBJ 12)) as Q12.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hpoff.
pose proof (RcLeafLib.rcl_cnt_range is_in bs k) as CI. pose proof (RcLeafLib.rcl_cnt_range is_out bs k) as CO.
destruct (rp_byte _ p bs (8 + k) HG ltac:(lia)) as [VBk BBk].
set (E := Eimg (Ereg regs (rp_extraL (bt bs (8 + k))))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rp_extraL (bt bs (8 + k)))) n)
  by (intros n Hn0; subst E; apply Eimg_low; exact Hn0).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E13 : ew E 13 = Z_to_bv 64 (cnt is_out bs k)) by (rewrite (EE 13%nat 13%bv) by reflexivity; exact G13).
assert (E15 : ew E 15 = Z_to_bv 64 (cnt is_in bs k)) by (rewrite (EE 15%nat 15%bv) by reflexivity; exact G15).
assert (E16 : ew E 16 = Z_to_bv 64 (p + 8 + Z.of_nat k)) by (rewrite (EE 16%nat 16%bv) by reflexivity; exact G16).
assert (E17 : ew E 17 = Z_to_bv 64 (12 - Z.of_nat k)) by (rewrite (EE 17%nat 17%bv) by reflexivity; exact G17).
assert (E32 : ew E 32 = Z_to_bv 64 RP_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bt bs (8 + k))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
split.
- rewrite restrict_mkst_fx. unfold ss_rpL. apply pa_entry_st_ok_full.
  + unfold rp_regsL.
    apply YI04.regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite G14, (rp_den_off E 32 0 RP_SB E32) by (unfold RP_SB; lia). unfold w64. f_equal; lia. }
    apply YI04.regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite G6, (rp_den_off E 16 0 (p + 8 + Z.of_nat k) E16) by lia. unfold w64. f_equal; lia. }
    apply YI04.regs_ok_pin; [|intros X; discriminate X|].
    2: { rewrite G12, (rp_den_off E 16 0 (p + 8 + Z.of_nat k) E16) by lia. unfold w64. f_equal; lia. }
    apply YI04.regs_ok_pin; [|intros X; discriminate X|cbn [sv_denot]; rewrite G7; reflexivity].
    apply YI04.regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite G5; reflexivity].
  + vm_compute. reflexivity.
  + unfold rp_bytL, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) RP_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RP_SB; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 16%nat (p + 8 + Z.of_nat k) E16) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (p + 8 + Z.of_nat k) 0 1 (SOff 33 0) (bt bs (8 + k)));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
      replace (p + 8 + Z.of_nat k + 0) with (p + Z.of_nat (8 + k)) by lia. exact VBk.
  + apply pairwise_disjoint_of_extents. unfold rp_bytL, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 16%nat (p + 8 + Z.of_nat k) E16) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rp_factsL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E13, E15, E16, E17, E32, E33, !unsigned_lit_small by (unfold RP_SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold RP_SB. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, rp_SHL. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E RP_Bx 16 p 20 (p + 8 + Z.of_nat k) 0 1 Hrad).
  + unfold U, RP_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold RP_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Ltac rp_env HS :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  lazymatch goal with HA0 : env_agree 32 ?R ?E0 |- _ =>
  lazymatch Ex with
  | E0 => idtac
  | _ =>
    let EA := fresh "EA" in
    assert (EA : forall n, (n < 300)%nat -> ew Ex n = ew E0 n)
      by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; cbn [ew ewset extK];
          repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end; reflexivity);
    repeat match goal with H : ew E0 ?n = ?v |- _ => rewrite <- (EA n ltac:(lia)) in H end;
    repeat match goal with H : bv_unsigned (ew E0 ?n) = ?v |- _ => rewrite <- (EA n ltac:(lia)) in H end;
    let H2 := fresh "HA" in
    assert (H2 : env_agree 32 R Ex)
      by (split; [let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; rewrite EA by lia; exact (proj1 HA0 n Hn)
                 | cbn [ed ewset extK]; exact (proj2 HA0)]);
    clear HA0 EA; rename H2 into HA0;
    let E1 := fresh "Ev" in let HE1 := fresh "HE" in remember Ex as E1 eqn:HE1; clear HE1
  end end end.
Ltac rp_mm :=
  lazymatch goal with HF : frame_of _ ?rs ?m1 (ms_mem ?m2), MM : forall x : word, ?m1 x = ?m0 x |- _ =>
  let MX := fresh "MX" in let MM2 := fresh "MM" in
  pose proof (rp_frame_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MX;
  assert (MM2 : forall x, ms_mem m2 x = m0 x) by (let x := fresh "x" in intros x; rewrite MX; apply MM);
  clear MX MM HF; try (match goal with H : frame_of _ _ _ _ |- _ => clear H end);
  try (match goal with H : mem_grows _ _ |- _ => clear H end); rename MM2 into MM end.
Definition rp_loop_post (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (STK sp0 : Z)
  (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
  (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (kj : Z) (bs : list byte) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst (fx := fx) regs' (Z_to_bv 64 (BASE + 0x87e0)) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' kj /\
    (forall rr, In rr RP_KEPT -> getr regs' rr = getr regs rr) /\
    getr regs' 15 = w64 (n_in bs) /\ getr regs' 13 = w64 (n_out bs) /\ (forall x, mem' x = mem x).
Lemma rp_loop : forall (n k : nat) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md kj
    (regs : bvmap 5 word) p (bs : list byte),
  (k + n = 12)%nat -> (0 < n)%nat ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj ->
  length bs = 20%nat -> 1 <= p -> p + 20 <= 2 ^ 47 -> off_img p 20 -> (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 20 ->
  garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) bs) ->
  getr regs 5 = w64 2 -> getr regs 6 = w64 (p + 8 + Z.of_nat k) -> getr regs 7 = w64 1 ->
  getr regs 12 = w64 (p + 8 + Z.of_nat k) -> getr regs 13 = w64 (cnt is_out bs k) -> getr regs 14 = w64 RP_SB ->
  getr regs 15 = w64 (cnt is_in bs k) -> getr regs 16 = w64 (p + 8 + Z.of_nat k) -> getr regs 17 = w64 (12 - Z.of_nat k) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x8778)) mem (seg_rom SEGS)) md)
    (rp_loop_post W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc kj bs).
Proof.
induction n as [|n IH]; intros k STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj regs p bs Hkn Hn HJ LB Hp1 Hp47
  Hpoff Hpz Hrad HG G5 G6 G7 G12 G13 G14 G15 G16 G17; [lia|].
pose proof (RcLeafLib.rcl_cnt_range is_in bs k) as CI. pose proof (RcLeafLib.rcl_cnt_range is_out bs k) as CO.
destruct (rp_byte _ p bs (8 + k) HG ltac:(lia)) as [VBk BBk].
destruct (rp_loop_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kj regs p bs k HJ ltac:(lia) LB Hp1 Hp47 Hpoff Hpz
  Hrad HG G5 G6 G7 G12 G13 G14 G15 G16 G17) as [HS SHOK].
remember (Eimg (Ereg regs (rp_extraL (bt bs (8 + k))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rp_extraL (bt bs (8 + k)))) E)
  by (subst E; split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n0 (rr : bv 5), Z.of_nat n0 = bv_unsigned rr -> ew E n0 = getr regs rr)
  by (intros n0 rr Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E13 : ew E 13 = Z_to_bv 64 (cnt is_out bs k)) by (rewrite (EE 13%nat 13%bv) by reflexivity; exact G13).
assert (E15 : ew E 15 = Z_to_bv 64 (cnt is_in bs k)) by (rewrite (EE 15%nat 15%bv) by reflexivity; exact G15).
assert (E16 : ew E 16 = Z_to_bv 64 (p + 8 + Z.of_nat k)) by (rewrite (EE 16%nat 16%bv) by reflexivity; exact G16).
assert (E17 : ew E 17 = Z_to_bv 64 (12 - Z.of_nat k)) by (rewrite (EE 17%nat 17%bv) by reflexivity; exact G17).
assert (E32 : ew E 32 = Z_to_bv 64 RP_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bt bs (8 + k)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (MM : forall x : word, mem x = mem x) by reflexivity.
clear EE HE.
paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
psrr_branch_tok RUN BR HS SHOK RP_Bspan.
- rewrite branch_eq_U, (U_atom _ 33 _ E33), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (NI : cnt is_in bs (Datatypes.S k) = cnt is_in bs k + 1) by (rewrite RcLeafLib.rcl_cnt_S, Hc; reflexivity).
  assert (NO : cnt is_out bs (Datatypes.S k) = cnt is_out bs k + 0) by (rewrite RcLeafLib.rcl_cnt_S, Hc; reflexivity).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
  psrr_branch_tok RUN BR HS SHOK RP_Bspan.
  { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
    assert (Hn' : (0 < n)%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [discriminate Hc | lia]). clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x8778; [rp_awr0|]. rp_mm. rp_env HS.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
      pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + k)))
        [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
      cbn [ms_regs restrict] in KR;
      prreg HS (5%bv : bv 5) Q5; prreg HS (6%bv : bv 5) Q6; prreg HS (7%bv : bv 5) Q7; prreg HS (12%bv : bv 5) Q12;
      prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16;
      prreg HS (17%bv : bv 5) Q17;
      pmkst HS;
      eapply SRr_mono;
      [ eapply (IH (Datatypes.S k) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msf) _ kj (ms_regs msf) p bs ltac:(lia) Hn' HJ
          LB Hp1 Hp47 Hpoff Hpz);
        [ apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hrad];
          let x := fresh "x" in intros x _; apply rp_aview_eq; exact MM
        | apply (garr8_frame SEGS (mrestrict (w_H W) mem)); [exact HG|];
          let a := fresh "a" in intros a _; apply (mbyte_of_aview SEGS); apply rp_aview_eq; exact MM
        | rewrite Q5; reflexivity
        | rewrite Q6, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
        | rewrite Q7; reflexivity
        | rewrite Q12, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
        | rewrite Q13, NO; first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity]
        | rewrite Q14, E32; reflexivity
        | rewrite Q15, NI; first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity]
        | rewrite Q16, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
        | rewrite Q17, E17, unsigned_lit_small by lia; unfold w64; f_equal; lia ]
      | let W' := fresh "W'" in let c' := fresh "c'" in let HP' := fresh "HP'" in
        intros W' c' _ HP'; unfold rp_loop_post in HP' |- *;
        destruct HP' as (-> & regs' & mem' & md' & -> & HJ' & HK' & H15' & H13' & HM');
        split; [reflexivity|]; exists regs', mem', md'; split; [reflexivity|]; split; [exact HJ'|];
        split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; rewrite (HK' rr Hrr); cbv [RP_KEPT In] in Hrr;
                 repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                 destruct Hrr |];
        split; [exact H15'|]; split; [exact H13'|];
        let x := fresh "x" in intros x; rewrite HM', MM; reflexivity ]
    end. }
  { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
    assert (Hn0 : n = 0%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [lia | discriminate Hc]). clear Hc. subst n.
    assert (Hk11 : k = 11%nat) by lia. subst k.
    paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x87e0; [rp_awr0|]. rp_mm. rp_env HS.
    lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
      pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + 11)))
        [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
      cbn [ms_regs restrict] in KR;
      prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15;
      pmkst HS; apply SRr_ret; unfold rp_loop_post; split; [reflexivity|];
      exists (ms_regs msf), (ms_mem msf); eexists; split; [reflexivity|]; split; [exact HJ|];
      split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; cbv [RP_KEPT In] in Hrr;
               repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
               destruct Hrr |];
      split; [ unfold n_in; rewrite Q15, NI;
               first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity] |];
      split; [ unfold n_out; rewrite Q13, NO;
               first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity] |];
      exact MM
    end. }
- rewrite branch_eq_U, (U_atom _ 33 _ E33), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into C2.
  paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
  psrr_branch_tok RUN BR HS SHOK RP_Bspan.
  + rewrite branch_eq_U, (U_atom _ 33 _ E33), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    assert (NI : cnt is_in bs (Datatypes.S k) = cnt is_in bs k + 0) by (rewrite RcLeafLib.rcl_cnt_S, Hc; reflexivity).
    assert (NO : cnt is_out bs (Datatypes.S k) = cnt is_out bs k + 1) by (rewrite RcLeafLib.rcl_cnt_S, Hc; reflexivity).
    clear Hc.
    paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
    psrr_branch_tok RUN BR HS SHOK RP_Bspan.
    { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
      assert (Hn' : (0 < n)%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [discriminate Hc | lia]). clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x8778; [rp_awr0|]. rp_mm. rp_env HS.
      lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
        pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + k)))
          [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
        cbn [ms_regs restrict] in KR;
        prreg HS (5%bv : bv 5) Q5; prreg HS (6%bv : bv 5) Q6; prreg HS (7%bv : bv 5) Q7; prreg HS (12%bv : bv 5) Q12;
        prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16;
        prreg HS (17%bv : bv 5) Q17;
        pmkst HS;
        eapply SRr_mono;
        [ eapply (IH (Datatypes.S k) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msf) _ kj (ms_regs msf) p bs ltac:(lia) Hn' HJ
            LB Hp1 Hp47 Hpoff Hpz);
          [ apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hrad];
            let x := fresh "x" in intros x _; apply rp_aview_eq; exact MM
          | apply (garr8_frame SEGS (mrestrict (w_H W) mem)); [exact HG|];
            let a := fresh "a" in intros a _; apply (mbyte_of_aview SEGS); apply rp_aview_eq; exact MM
          | rewrite Q5; reflexivity
          | rewrite Q6, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | rewrite Q7; reflexivity
          | rewrite Q12, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | rewrite Q13, NO; first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity]
          | rewrite Q14, E32; reflexivity
          | rewrite Q15, NI; first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity]
          | rewrite Q16, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | rewrite Q17, E17, unsigned_lit_small by lia; unfold w64; f_equal; lia ]
        | let W' := fresh "W'" in let c' := fresh "c'" in let HP' := fresh "HP'" in
          intros W' c' _ HP'; unfold rp_loop_post in HP' |- *;
          destruct HP' as (-> & regs' & mem' & md' & -> & HJ' & HK' & H15' & H13' & HM');
          split; [reflexivity|]; exists regs', mem', md'; split; [reflexivity|]; split; [exact HJ'|];
          split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; rewrite (HK' rr Hrr); cbv [RP_KEPT In] in Hrr;
                   repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                   destruct Hrr |];
          split; [exact H15'|]; split; [exact H13'|];
          let x := fresh "x" in intros x; rewrite HM', MM; reflexivity ]
      end. }
    { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
      assert (Hn0 : n = 0%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [lia | discriminate Hc]). clear Hc. subst n.
      assert (Hk11 : k = 11%nat) by lia. subst k.
      paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x87e0; [rp_awr0|]. rp_mm. rp_env HS.
      lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
        pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + 11)))
          [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
        cbn [ms_regs restrict] in KR;
        prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15;
        pmkst HS; apply SRr_ret; unfold rp_loop_post; split; [reflexivity|];
        exists (ms_regs msf), (ms_mem msf); eexists; split; [reflexivity|]; split; [exact HJ|];
        split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; cbv [RP_KEPT In] in Hrr;
                 repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                 destruct Hrr |];
        split; [ unfold n_in; rewrite Q15, NI;
                 first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity] |];
        split; [ unfold n_out; rewrite Q13, NO;
                 first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity] |];
        exact MM
      end. }
  + rewrite branch_eq_U, (U_atom _ 33 _ E33), U_lit in Hc by lia. apply Z.eqb_neq in Hc. rename Hc into C1.
    paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
    psrr_branch_tok RUN BR HS SHOK RP_Bspan.
    * rewrite branch_ne_U, (U_atom _ 33 _ E33), U_lit in Hc by lia.
      apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. rename Hc into C0.
      assert (NI : cnt is_in bs (Datatypes.S k) = cnt is_in bs k + 0)
        by (rewrite RcLeafLib.rcl_cnt_S; unfold is_in; rewrite (proj2 (Z.eqb_neq _ _) C0), (proj2 (Z.eqb_neq _ _) C2); reflexivity).
      assert (NO : cnt is_out bs (Datatypes.S k) = cnt is_out bs k + 0)
        by (rewrite RcLeafLib.rcl_cnt_S; unfold is_out; rewrite (proj2 (Z.eqb_neq _ _) C1); reflexivity).
      paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
      psrr_branch_tok RUN BR HS SHOK RP_Bspan.
      { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
        assert (Hn' : (0 < n)%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [discriminate Hc | lia]). clear Hc.
        paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x8778; [rp_awr0|]. rp_mm. rp_env HS.
        lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
          pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + k)))
            [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
          cbn [ms_regs restrict] in KR;
          prreg HS (5%bv : bv 5) Q5; prreg HS (6%bv : bv 5) Q6; prreg HS (7%bv : bv 5) Q7; prreg HS (12%bv : bv 5) Q12;
          prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16;
          prreg HS (17%bv : bv 5) Q17;
          pmkst HS;
          eapply SRr_mono;
          [ eapply (IH (Datatypes.S k) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msf) _ kj (ms_regs msf) p bs ltac:(lia) Hn' HJ
              LB Hp1 Hp47 Hpoff Hpz);
            [ apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hrad];
              let x := fresh "x" in intros x _; apply rp_aview_eq; exact MM
            | apply (garr8_frame SEGS (mrestrict (w_H W) mem)); [exact HG|];
              let a := fresh "a" in intros a _; apply (mbyte_of_aview SEGS); apply rp_aview_eq; exact MM
            | rewrite Q5; reflexivity
            | rewrite Q6, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | rewrite Q7; reflexivity
            | rewrite Q12, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | rewrite Q13, NO; first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity]
            | rewrite Q14, E32; reflexivity
            | rewrite Q15, NI; first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity]
            | rewrite Q16, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | rewrite Q17, E17, unsigned_lit_small by lia; unfold w64; f_equal; lia ]
          | let W' := fresh "W'" in let c' := fresh "c'" in let HP' := fresh "HP'" in
            intros W' c' _ HP'; unfold rp_loop_post in HP' |- *;
            destruct HP' as (-> & regs' & mem' & md' & -> & HJ' & HK' & H15' & H13' & HM');
            split; [reflexivity|]; exists regs', mem', md'; split; [reflexivity|]; split; [exact HJ'|];
            split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; rewrite (HK' rr Hrr); cbv [RP_KEPT In] in Hrr;
                     repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                     destruct Hrr |];
            split; [exact H15'|]; split; [exact H13'|];
            let x := fresh "x" in intros x; rewrite HM', MM; reflexivity ]
        end. }
      { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
        assert (Hn0 : n = 0%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [lia | discriminate Hc]). clear Hc. subst n.
        assert (Hk11 : k = 11%nat) by lia. subst k.
        paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x87e0; [rp_awr0|]. rp_mm. rp_env HS.
        lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
          pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + 11)))
            [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
          cbn [ms_regs restrict] in KR;
          prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15;
          pmkst HS; apply SRr_ret; unfold rp_loop_post; split; [reflexivity|];
          exists (ms_regs msf), (ms_mem msf); eexists; split; [reflexivity|]; split; [exact HJ|];
          split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; cbv [RP_KEPT In] in Hrr;
                   repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                   destruct Hrr |];
          split; [ unfold n_in; rewrite Q15, NI;
                   first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity] |];
          split; [ unfold n_out; rewrite Q13, NO;
                   first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity] |];
          exact MM
        end. }
    * rewrite branch_ne_U, (U_atom _ 33 _ E33), U_lit in Hc by lia.
      apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
      assert (NI : cnt is_in bs (Datatypes.S k) = cnt is_in bs k + 1) by (rewrite RcLeafLib.rcl_cnt_S, Hc; reflexivity).
      assert (NO : cnt is_out bs (Datatypes.S k) = cnt is_out bs k + 0) by (rewrite RcLeafLib.rcl_cnt_S, Hc; reflexivity).
      clear Hc.
      paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr0|]. rp_mm. rp_env HS.
      psrr_branch_tok RUN BR HS SHOK RP_Bspan.
      { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
        assert (Hn' : (0 < n)%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [discriminate Hc | lia]). clear Hc.
        paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x8778; [rp_awr0|]. rp_mm. rp_env HS.
        lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
          pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + k)))
            [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
          cbn [ms_regs restrict] in KR;
          prreg HS (5%bv : bv 5) Q5; prreg HS (6%bv : bv 5) Q6; prreg HS (7%bv : bv 5) Q7; prreg HS (12%bv : bv 5) Q12;
          prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16;
          prreg HS (17%bv : bv 5) Q17;
          pmkst HS;
          eapply SRr_mono;
          [ eapply (IH (Datatypes.S k) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msf) _ kj (ms_regs msf) p bs ltac:(lia) Hn' HJ
              LB Hp1 Hp47 Hpoff Hpz);
            [ apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hrad];
              let x := fresh "x" in intros x _; apply rp_aview_eq; exact MM
            | apply (garr8_frame SEGS (mrestrict (w_H W) mem)); [exact HG|];
              let a := fresh "a" in intros a _; apply (mbyte_of_aview SEGS); apply rp_aview_eq; exact MM
            | rewrite Q5; reflexivity
            | rewrite Q6, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | rewrite Q7; reflexivity
            | rewrite Q12, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | rewrite Q13, NO; first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity]
            | rewrite Q14, E32; reflexivity
            | rewrite Q15, NI; first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity]
            | rewrite Q16, E16, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | rewrite Q17, E17, unsigned_lit_small by lia; unfold w64; f_equal; lia ]
          | let W' := fresh "W'" in let c' := fresh "c'" in let HP' := fresh "HP'" in
            intros W' c' _ HP'; unfold rp_loop_post in HP' |- *;
            destruct HP' as (-> & regs' & mem' & md' & -> & HJ' & HK' & H15' & H13' & HM');
            split; [reflexivity|]; exists regs', mem', md'; split; [reflexivity|]; split; [exact HJ'|];
            split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; rewrite (HK' rr Hrr); cbv [RP_KEPT In] in Hrr;
                     repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                     destruct Hrr |];
            split; [exact H15'|]; split; [exact H13'|];
            let x := fresh "x" in intros x; rewrite HM', MM; reflexivity ]
        end. }
      { rewrite branch_ne_U, (U_atom_off _ 17 (12 - Z.of_nat k) (-1) E17), U_lit in Hc by lia.
        assert (Hn0 : n = 0%nat) by (destruct (Z.eqb_spec (12 - Z.of_nat k + -1) 0); [lia | discriminate Hc]). clear Hc. subst n.
        assert (Hk11 : k = 11%nat) by lia. subst k.
        paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x87e0; [rp_awr0|]. rp_mm. rp_env HS.
        lazymatch goal with HS : st_ok_pi _ _ _ ?ssf (restrict _ ?msf) |- _ =>
          pose proof (regs_kept_of_st_ok_pi _ ssf _ regs (rp_extraL (bt bs (8 + 11)))
            [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as KR;
          cbn [ms_regs restrict] in KR;
          prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (15%bv : bv 5) Q15;
          pmkst HS; apply SRr_ret; unfold rp_loop_post; split; [reflexivity|];
          exists (ms_regs msf), (ms_mem msf); eexists; split; [reflexivity|]; split; [exact HJ|];
          split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr; cbv [RP_KEPT In] in Hrr;
                   repeat (destruct Hrr as [<-|Hrr]; [first [apply KR; cbv; tauto | rewrite Q14, E32, G14; reflexivity] |]);
                   destruct Hrr |];
          split; [ unfold n_in; rewrite Q15, NI;
                   first [rewrite E15; unfold w64; f_equal; lia | rewrite E15, unsigned_lit_small by lia; reflexivity] |];
          split; [ unfold n_out; rewrite Q13, NO;
                   first [rewrite E13; unfold w64; f_equal; lia | rewrite E13, unsigned_lit_small by lia; reflexivity] |];
          exact MM
        end. }
Qed.
Lemma rp_after : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p q : Z) (bs : list byte) (E : env) ms md,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q ->
  sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  1 <= p -> 4 <= q -> q + 12 <= 2 ^ 47 -> off_img q 12 ->
  length bs = 20%nat -> p + 20 <= 2 ^ 47 -> off_img p 20 -> (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) ->
  (spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20 ->
  garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs) ->
  (q + 12 <= p \/ p + 20 <= q) -> (q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 12 ->
  (forall a, q <= a < q + 12 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall a, q <= a < q + 12 -> ~ in_img SEGS a) ->
  (forall a, q <= a < q + 12 -> apresent (w_H W) memc a) ->
  ports_ok p q bs = true ->
  img_env VAL A_LIM E -> env_agree 32 (Ereg regs (rp_extra bs)) E ->
  ew E 32 = Z_to_bv 64 RP_SB -> ew E 36 = Z_to_bv 64 (bt bs 7) ->
  st_ok_pi SEGS VAL E ss_rpLH (restrict (w_H W) ms) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  rp_kept W (spZ regs) memc (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs E ms md HJc Hra H10 H11 Hslo Hshi Hqsp Hp1 Hq4
  Hq47 Hqoff LB Hp47 Hpoff Hpz Hpsp Hradp HGp Hpq Hqz Hradq Hwr HqI Hqpres Hok HEI HAE E32 E36 HS HJ KC.
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hs16 & Hstk0 & Hceil & Hlo0 & Hhi0 & H47 & _).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 12)) as RV12.
pose proof Hqoff as Hqoff'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, Hqoff'.
pose proof (RcLeafLib.rcl_cnt_range is_in bs 12) as CI. pose proof (RcLeafLib.rcl_cnt_range is_out bs 12) as CO.
change (cnt is_in bs 12) with (n_in bs) in CI. change (cnt is_out bs 12) with (n_out bs) in CO.
change (Z.of_nat 12) with 12 in CI, CO.
destruct (rp_byte _ p bs 7 HGp ltac:(lia)) as [_ B7].
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite (proj1 HAE 10%nat ltac:(lia)), (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 q)
  by (rewrite (proj1 HAE 11%nat ltac:(lia)), (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (rewrite <- (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (rewrite <- (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hq0 : 0 <= q) by lia. assert (Hq63 : q + 12 <= 2 ^ 63) by lia.
assert (SHX : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
   ~ (spZ regs - 16 <= shadow_of_addr SHADOW_OFF x < spZ regs)).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_le_mono 0 x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  change (2 ^ 47 / 8) with (2 ^ 44) in *. change (0 / 8) with 0 in *. lia. }
assert (HradpM : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF p 20).
{ apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact Hradp]. intros x Hx.
  destruct (SHX x ltac:(lia)) as [S1 S2]. exact (proj1 KC _ S1 S2). }
assert (HGM : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) p (map (fun b : byte => bv_unsigned b) bs)).
{ apply (garr8_frame SEGS (mrestrict (w_H W) memc)); [exact HGp|]. intros a Ha. rewrite length_map, LB in Ha.
  apply (mbyte_of_aview SEGS). apply (proj1 KC); lia. }
prreg HS (5%bv : bv 5) Q5. prreg HS (6%bv : bv 5) Q6. prreg HS (7%bv : bv 5) Q7. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (16%bv : bv 5) Q16.
prreg HS (17%bv : bv 5) Q17.
pmkst HS.
try (replace (ss_pc ss_rpLH) with 0x8778 by reflexivity).
eapply SRr_bind.
{ eapply (rp_loop 12 0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) _ k (ms_regs ms) p bs eq_refl ltac:(lia) HJ LB
    Hp1 Hp47 Hpoff Hpz HradpM HGM);
  [ rewrite Q5; reflexivity
  | rewrite Q6, E10, unsigned_lit_small by lia; unfold w64; f_equal; lia
  | rewrite Q7; reflexivity
  | rewrite Q12, E10, unsigned_lit_small by lia; unfold w64; f_equal; lia
  | rewrite Q13; reflexivity
  | rewrite Q14, E32; reflexivity
  | rewrite Q15; reflexivity
  | rewrite Q16, E10, unsigned_lit_small by lia; unfold w64; f_equal; lia
  | rewrite Q17; reflexivity ]. }
cbv beta. intros W' c' _ HPL. unfold rp_loop_post in HPL.
destruct HPL as (-> & regsL & memL & mdL & -> & HJL & HKL & HL15 & HL13 & HML).
jafter_stretch_pi HS 40%nat regsL (mrestrict (w_H W) memL) RP_CLOB 0x87e0 HS2.
match type of HS2 with ?A1 -> _ => assert (HRR : A1); [|specialize (HS2 HRR); clear HRR] end.
{ intros rr Hrr. cbn [ms_regs restrict]. destruct (rp_clob_cases rr Hrr) as [-> | Hk];
  [rewrite !getr_zero; reflexivity | exact (HKL rr Hk)]. }
match type of HS2 with ?A1 -> _ => assert (HRK : A1); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (apply (region_kept_aview _ (w_H W) (ms_mem ms) memL _ _ _ _ _ _ _ eq_refl);
   [intros a _; apply rp_aview_eq; exact HML | intros a; apply rp_apres_eq; exact HML]). }
rewrite <- restrict_mkst_fx in HS2.
lazymatch type of HS2 with st_ok_pi _ _ (havoc ?Eh 40 ?wsh) _ _ =>
  remember (havoc Eh 40 wsh) as Ev2 eqn:HE2 in HS2 end.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 40)%nat -> ew Ev2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (rp_extra bs)) Ev2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (F44 : ew Ev2 44 = Z_to_bv 64 (n_out bs)).
{ rewrite HE2. replace 44%nat with (40 + 4)%nat by reflexivity.
  rewrite (ew_havoc_new E 40 (map (getr regsL) RP_CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia). cbn [nth map RP_CLOB]. exact HL13. }
assert (F45 : ew Ev2 45 = Z_to_bv 64 (n_in bs)).
{ rewrite HE2. replace 45%nat with (40 + 5)%nat by reflexivity.
  rewrite (ew_havoc_new E 40 (map (getr regsL) RP_CLOB) 5 (Z_to_bv 64 0)) by (cbn; lia). cbn [nth map RP_CLOB]. exact HL15. }
assert (F1 : ew Ev2 1 = getr regs 1) by (rewrite OLD2 by lia; exact E1).
assert (F10 : ew Ev2 10 = Z_to_bv 64 p) by (rewrite OLD2 by lia; exact E10).
assert (F11 : ew Ev2 11 = Z_to_bv 64 q) by (rewrite OLD2 by lia; exact E11).
assert (F32 : ew Ev2 32 = Z_to_bv 64 RP_SB) by (rewrite OLD2 by lia; exact E32).
assert (F36 : ew Ev2 36 = Z_to_bv 64 (bt bs 7)) by (rewrite OLD2 by lia; exact E36).
assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (FO0 : ew Ev2 (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (rewrite HE2, ew_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia); exact EO0).
assert (FO12 : ew Ev2 (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (rewrite HE2, ew_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia); exact EO12).
assert (Uq : bv_unsigned (ew Ev2 11) = q) by (rewrite F11; apply unsigned_lit_small; lia).
clear HE2.
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss2 ?ms2 =>
  pose proof (st_ok_pi_add_fact Ev2 ss2 ms2 44 (mkAF 0 12 0) HS2
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite F44, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r;
          repeat split; lia)) as HS3 end.
clear HS2.
lazymatch type of HS3 with st_ok_pi _ _ _ ?ss3 ?ms3 =>
  pose proof (st_ok_pi_add_fact Ev2 ss3 ms3 45 (mkAF 0 12 0) HS3
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite F45, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r;
          repeat split; lia)) as HS4 end.
clear HS3.
assert (KL : rp_kept W (spZ regs) memc memL) by (exact (rp_kept_eq W (spZ regs) memc (ms_mem ms) memL KC HML)).
lazymatch type of HS4 with st_ok_pi _ _ _ ?ss4 ?ms4 =>
  pose proof (st_ok_pi_add_region Ev2 ss4 ms4 rp_qreg HS4 eq_refl) as HS5 end.
match type of HS5 with ?A1 -> _ => assert (HRO : A1); [|specialize (HS5 HRO); clear HRO] end.
{ unfold region_ok, rp_qreg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite F11, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (proj2 KL). apply Hqpres. lia. }
match type of HS5 with ?A1 -> _ => assert (HRD : A1); [|specialize (HS5 HRD); clear HRD] end.
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint, rp_qreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  change (ew Ev2 241) with (ew Ev2 (A_OBJ 0)). change (ew Ev2 253) with (ew Ev2 (A_OBJ 12)).
  rewrite F11, F10, FO0, FO12, Usp2, !unsigned_lit_small by lia.
  repeat split; lia. }
clear HS4.
assert (HradqL : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF q 12).
{ apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact Hradq]. intros x Hx.
  destruct (SHX x ltac:(lia)) as [S1 S2]. exact (proj1 KL _ S1 S2). }
assert (HradpL : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF p 20).
{ apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact Hradp]. intros x Hx.
  destruct (SHX x ltac:(lia)) as [S1 S2]. exact (proj1 KL _ S1 S2). }
assert (SHOKL : sh_ok SEGS RP_Bx rp_SH Ev2 (mrestrict (w_H W) memL)).
{ unfold sh_ok, rp_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H W) memL Ev2 RP_Bx 10 p 20 p 0 20 HradpL).
    + unfold U, RP_Bx. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold RP_SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite F10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W) memL Ev2 RP_Bx 11 q 12 q 0 12 HradqL).
    + unfold U, RP_Bx. cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold RP_SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite F11, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (KQ : rp_keptQ W (spZ regs) q memc memL)
  by (split; [intros a Ha Hs _; exact (proj1 KL a Ha Hs) | exact (proj2 KL)]).
clear HS HAE.
rename HAE2 into HAE.
paj_run_tok RUN HS5 HJL SHOKL RP_Bspan; [rp_awrQ Usp2 (spZ regs) sp0 q Uq Hwr|].
rp_keepQ Usp2 Uq KQ. rp_env HS5.
psrr_branch_tok RUN BR HS5 SHOKL RP_Bspan.
{ exfalso. rewrite branch_ne_U, (rp_U_c30 _ 45 (n_in bs) F45 ltac:(lia)), U_lit in Hc by lia. cbn in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS5 HJL SHOKL RP_Bspan; [rp_awrQ Usp2 (spZ regs) sp0 q Uq Hwr|].
rp_keepQ Usp2 Uq KQ. rp_env HS5.
psrr_branch_tok RUN BR HS5 SHOKL RP_Bspan.
{ exfalso. rewrite branch_ne_U, (rp_U_c30 _ 44 (n_out bs) F44 ltac:(lia)), U_lit in Hc by lia. cbn in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS5 HJL SHOKL RP_Bspan; [rp_awrQ Usp2 (spZ regs) sp0 q Uq Hwr|].
rp_keepQ Usp2 Uq KQ. rp_env HS5.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10;
  pose proof (st_ok_pi_region_nth Ex ssx _ 0
    (YP09.mkRegion (Some 11%nat) 0 12 0 12
      [YP09.mkChunk 8 (CVal 4 (SAlu ALU_SLL (SOff 36 0) (SLit 4))); YP09.mkChunk 4 (CVal 4 (SAlu ALU_SLL (SOff 44 0) (SLit 2)));
       YP09.mkChunk 0 (CVal 4 (SAlu ALU_SLL (SOff 45 0) (SLit 2)))]) HS ltac:(vm_compute; reflexivity)) as RQ;
  cbn [ms_mem restrict] in RQ;
  assert (VQ0 : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (q + 0) 4 (4 * n_in bs))
    by exact (field_of_region Ex _ 11 q _ 0 12 0 12 0 4 _ _ RQ Uq ltac:(right; right; left; reflexivity)
                (rp_den_sll2 Ex 45 (n_in bs) F45 ltac:(lia)) ltac:(lia) ltac:(lia));
  assert (VQ4 : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (q + 4) 4 (4 * n_out bs))
    by exact (field_of_region Ex _ 11 q _ 0 12 0 12 4 4 _ _ RQ Uq ltac:(right; left; reflexivity)
                (rp_den_sll2 Ex 44 (n_out bs) F44 ltac:(lia)) ltac:(lia) ltac:(lia));
  assert (VQ8 : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (q + 8) 4 (16 * bt bs 7))
    by exact (field_of_region Ex _ 11 q _ 0 12 0 12 8 4 _ _ RQ Uq ltac:(left; reflexivity)
                (rp_den_sll4 Ex 36 (bt bs 7) F36 ltac:(lia)) ltac:(lia) ltac:(lia));
  rewrite Z.add_0_r in VQ0;
  eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat := fresh "mat" in intros mat;
  apply (rp_post_build _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msc) _ (ms_regs msc) _ (fun a => q <= a < q + 12) HJc
     ltac:(apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJL) Hslo Hshi Hq0 Hq63 Hqsp);
  [ intros a Ha; exact Ha
  | intros a Ha; exact (HqI a Ha)
  | intros a Ha Hs Hq; exact (proj1 KQ a Ha Hs Hq)
  | exact (proj2 KQ)
  | cbn [ms_regs]; rewrite Q1, F1; exact Hra
  | eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ _ _ HS); [exact HAE | vm_compute; reflexivity]
  | rewrite Hok; cbn [ms_regs]; rewrite Q10; reflexivity
  | rewrite Hok; split; [exact VQ0|]; split; [exact VQ4 | exact VQ8] ]
end.
Qed.
Lemma rp_main : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (p q : Z) (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  1 <= p -> 4 <= q -> q + 12 <= 2 ^ 47 -> off_img q 12 ->
  length bs = 20%nat -> p + 20 <= 2 ^ 47 -> off_img p 20 -> (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) ->
  (spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20 ->
  garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs) ->
  q mod 4 = 0 -> (q + 12 <= p \/ p + 20 <= q) -> (q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 12 ->
  (forall a, q <= a < q + 12 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  (forall a, q <= a < q + 12 -> ~ in_img SEGS a) ->
  (forall a, q <= a < q + 12 -> apresent (w_H W) memc a) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hra H10 H11 Hal16 Hslo Hshi Hqsp
  Hp1 Hq4 Hq47 Hqoff LB Hp47 Hpoff Hpz Hpsp Hradp HGp Hq4m Hpq Hqz Hradq Hwr HqI Hqpres.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
assert (WS : REAC_PORTS_PARSE_STK = 4112) by reflexivity.
pose proof HJ as HJc.
assert (Hq0 : 0 <= q) by lia. assert (Hq63 : q + 12 <= 2 ^ 63) by lia.
destruct (rp_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hal16 Hslo Hshi H10 H11 Hp1 Hp47
  Hq4 Hq47 Hq4m Hpsp Hpoff Hpz LB Hradp HGp) as [HS SHOK].
destruct (rp_byte _ p bs 0 HGp ltac:(lia)) as [_ B0].
destruct (rp_byte _ p bs 1 HGp ltac:(lia)) as [_ B1].
destruct (rp_byte _ p bs 4 HGp ltac:(lia)) as [_ B4].
assert (Pf : (p =? 0) = false) by (apply Z.eqb_neq; lia).
assert (Qf : (q =? 0) = false) by (apply Z.eqb_neq; lia).
remember (Eimg (Ereg regs (rp_extra bs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rp_extra bs)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (apply (EE 1%nat 1%bv); reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (bt bs 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bt bs 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bt bs 4)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E32 : ew E 32 = Z_to_bv 64 RP_SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E36 : ew E 36 = Z_to_bv 64 (bt bs 7)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (KC : rp_kept W (spZ regs) memc memc) by (split; [intros; reflexivity | intros a Ha; exact Ha]).
clear EE HE.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_ports_parse)) with (Z_to_bv 64 (BASE + AF_both3_reac_ports_parse)).
paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|].
rp_keep Usp KC. rp_env HS.
psrr_branch_tok RUN BR HS SHOK RP_Bspan.
{ rewrite branch_ne_U, (U_atom _ 33 (bt bs 0) E33), U_lit in Hc by lia.
  apply negb_true_iff in Hc.
  assert (Hok : ports_ok p q bs = false) by (unfold ports_ok, decl; rewrite Pf, Qf, Hc; reflexivity).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
  rp_fail HS HJ HJc KC Hok Hra Hslo Hshi Hq0 Hq63 Hqsp E1 HAE Hsegs. }
rewrite branch_ne_U, (U_atom _ 33 (bt bs 0) E33), U_lit in Hc by lia.
apply negb_false_iff in Hc. rename Hc into X0.
paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
psrr_branch_tok RUN BR HS SHOK RP_Bspan.
{ rewrite branch_ne_U, (U_atom _ 34 (bt bs 1) E34), U_lit in Hc by lia.
  apply negb_true_iff in Hc.
  assert (Hok : ports_ok p q bs = false) by (unfold ports_ok, decl; rewrite Pf, Qf, X0, Hc; reflexivity).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
  rp_fail HS HJ HJc KC Hok Hra Hslo Hshi Hq0 Hq63 Hqsp E1 HAE Hsegs. }
rewrite branch_ne_U, (U_atom _ 34 (bt bs 1) E34), U_lit in Hc by lia.
apply negb_false_iff in Hc. rename Hc into X1.
paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
psrr_branch_tok RUN BR HS SHOK RP_Bspan.
{ rewrite branch_eq_U, (U_atom _ 35 (bt bs 4) E35), U_lit in Hc by lia. rename Hc into X4.
  assert (Hok : ports_ok p q bs = true) by (unfold ports_ok, decl; rewrite Pf, Qf, X0, X1, X4, orb_true_r; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x8778; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
    pose proof (st_ok_pi_facts_incl Ex ssx _ (f_atoms rp_facts) [] HS
      ltac:(intros x Hx; vm_compute; vm_compute in Hx; exact Hx) ltac:(intros x Hx; destruct Hx)) as HSL;
    replace (set_facts ssx (mkFacts (f_atoms rp_facts) [] [])) with ss_rpLH in HSL by (vm_compute; reflexivity);
    lazymatch goal with HEIx : img_env _ _ Ex |- _ =>
    exact (rp_after STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs Ex msc _ HJc Hra H10 H11 Hslo Hshi Hqsp
      Hp1 Hq4 Hq47 Hqoff LB Hp47 Hpoff Hpz Hpsp Hradp HGp Hpq Hqz Hradq Hwr HqI Hqpres Hok HEIx HAE E32 E36 HSL HJ KC) end
  end. }
rewrite branch_eq_U, (U_atom _ 35 (bt bs 4) E35), U_lit in Hc by lia.
apply Z.eqb_neq in Hc. rename Hc into X4.
paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
psrr_branch_tok RUN BR HS SHOK RP_Bspan.
{ rewrite branch_ne_U, (rp_U_or4 _ 35 (bt bs 4) E35 B4), U_lit in Hc by lia.
  apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
  assert (Hok : ports_ok p q bs = false).
  { unfold ports_ok, decl. rewrite Pf, Qf, X0, X1, (proj2 (Z.eqb_neq _ 130) X4).
    destruct (Z.eqb_spec (bt bs 4) 128) as [Y|Y]; [exfalso; apply Hc; rewrite Y; reflexivity|].
    destruct (Z.eqb_spec (bt bs 4) 132) as [Y'|Y']; [exfalso; apply Hc; rewrite Y'; reflexivity|].
    reflexivity. }
  paj_run_tok RUN HS HJ SHOK RP_Bspan; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
  rp_fail HS HJ HJc KC Hok Hra Hslo Hshi Hq0 Hq63 Hqsp E1 HAE Hsegs. }
rewrite branch_ne_U, (rp_U_or4 _ 35 (bt bs 4) E35 B4), U_lit in Hc by lia.
apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
assert (Hok : ports_ok p q bs = true).
{ unfold ports_ok, decl. rewrite Pf, Qf, X0, X1.
  destruct (rp_lor4 (bt bs 4) B4 Hc) as [Y|Y]; rewrite Y; reflexivity. }
paj_run_to_tok RUNTO HS HJ SHOK RP_Bspan 0x8778; [rp_awr Usp (spZ regs) sp0|]. rp_keep Usp KC. rp_env HS.
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  pose proof (st_ok_pi_facts_incl Ex ssx _ (f_atoms rp_facts) [] HS
    ltac:(intros x Hx; vm_compute; vm_compute in Hx; exact Hx) ltac:(intros x Hx; destruct Hx)) as HSL;
  replace (set_facts ssx (mkFacts (f_atoms rp_facts) [] [])) with ss_rpLH in HSL by (vm_compute; reflexivity);
  lazymatch goal with HEIx : img_env _ _ Ex |- _ =>
  exact (rp_after STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs Ex msc _ HJc Hra H10 H11 Hslo Hshi Hqsp
    Hp1 Hq4 Hq47 Hqoff LB Hp47 Hpoff Hpz Hpsp Hradp HGp Hpq Hqz Hradq Hwr HqI Hqpres Hok HEIx HAE E32 E36 HSL HJ KC) end
end.
Qed.
Lemma rp_walk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (p q : Z) (bs : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 q -> 0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_PORTS_PARSE_STK -> spZ regs <= sp0 ->
  q + 12 <= 2 ^ 63 ->
  (spZ regs <= q \/ q + 12 <= spZ regs - REAC_PORTS_PARSE_STK) ->
  (p <> 0 -> q <> 0 ->
     length bs = 20%nat /\ p + 20 <= 2 ^ 47 /\ off_img p 20 /\
     (p + 20 <= kLowShadowBeg \/ kHighMemBeg <= p) /\
     (spZ regs <= p \/ p + 20 <= spZ regs - REAC_PORTS_PARSE_STK) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 20 /\
     (forall a, p <= a < p + 20 -> apresent (w_H W) memc a) /\
     garr8 SEGS (mrestrict (w_H W) memc) p (map (fun b : byte => bv_unsigned b) bs) /\
     q mod 4 = 0 /\ (q + 12 <= p \/ p + 20 <= q) /\
     (q + 12 <= kLowShadowBeg \/ kHighMemBeg <= q) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 12 /\
     (forall a, q <= a < q + 12 ->
        awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a)) ->
  SRr SEGS W (cfg_at (fx := fx) SEGS (BASE + AF_both3_reac_ports_parse) regs memc mdc)
    (treac_ports_parse_post fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p q bs).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch p q bs HJ HROD Hra Hra4 Hgp Htp H10 H11 Hp Hq Hch
  Hal16 Hslo Hshi Hq63 Hqsp HPQ.
destruct (Z.eq_dec p 0) as [P0|P0].
{ exact (rp_zero STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hra H10 H11 Hp Hq Hal16 Hslo Hshi
    Hq63 Hqsp (or_introl P0)). }
destruct (Z.eq_dec q 0) as [Q0|Q0].
{ exact (rp_zero STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hra H10 H11 Hp Hq Hal16 Hslo Hshi
    Hq63 Hqsp (or_intror Q0)). }
destruct (HPQ P0 Q0) as (LB & Hp47 & Hpoff & Hpz & Hpsp & Hradp & _ & HGp & Hq4m & Hpq & Hqz & Hradq & Hwrq).
assert (Hwr : forall a, q <= a < q + 12 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)
  by (intros a Ha; exact (proj1 (Hwrq a Ha))).
pose proof (rp_q_off STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k q HJ Hqz Hwr) as Hqo.
assert (Hq47 : q + 12 <= 2 ^ 47) by (destruct (Hqo (q + 11) ltac:(lia)) as (_ & H & _); lia).
assert (Hqoff : off_img q 12).
{ unfold off_img. destruct (Z_le_gt_dec (q + 12) YImgTop.IMG_LO) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec YImgTop.IMG_TOP q) as [H2|H2]; [right; exact H2|]. exfalso.
  destruct (Hqo (Z.max q YImgTop.IMG_LO) ltac:(lia)) as ([H3|H3] & _); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia. }
assert (Hq4 : 4 <= q) by (pose proof (Z.div_mod q 4 ltac:(lia)) as D; rewrite Hq4m in D; lia).
apply (rp_main STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p q bs HJ Hra H10 H11 Hal16 Hslo Hshi Hqsp
  ltac:(lia) Hq4 Hq47 Hqoff LB Hp47 Hpoff Hpz Hpsp Hradp HGp Hq4m Hpq Hqz Hradq Hwr
  (fun a Ha => proj2 (proj2 (Hqo a Ha))) (fun a Ha => proj2 (Hwrq a Ha))).
Qed.
End w.
Theorem pb_reac_ports_parse : treac_ports_parse_spec.
Proof. intros fq. exact (rp_walk (fx := fq)). Qed.
End h.
End f.
End d.
