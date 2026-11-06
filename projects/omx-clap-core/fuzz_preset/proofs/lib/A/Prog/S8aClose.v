(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): pieces 9 + 10 of
   the walk of ex_value (the internal file PIECES.md :69-70), against the frozen interface S8aIface.v, at L := A_prog_listing,
   PA := PI_prog_A, PI := prh_img_A, cp := CfParams_preset (ev_mid's prh_ledger reads alloc.c's statics at pi_g_* and
   the harness heads at cf_head before a block: a generic PrhImg / CfParams does not place them away from in's
   fields).
   - piece 10, ev_items_end (0x83cec-0x83d44 and the report arms 0x83e6c-0x83e7c, 0x83ed8-0x83ee4, 0x84008; 33
     instructions): ev_items_end_holds_zb : s8c_ZB -> ev_items_end_spec (P_END -> P_EXIT), three arms:
     v' = 0 (s8c_end_z), v' <> 0 with the machine's 64-bit `beq a1, a0` taken (s8c_end_veq) or not (s8c_end_vne).
   - piece 9, ev_items_close (0x83cb8-0x83ce8 and the report arms 0x83ecc-0x83ed4, 0x84020-0x84024; 18
     instructions): ev_items_close_holds_zb : s8c_ZB -> ev_items_close_spec (P_CLOSE -> P_EXIT), two arms: the byte
     is not the closer (refusal, s11 = -1 at 0x83cc8, s8c_close_refuse) or is (in->p := x0 + i + 1, a1 := length
     acc, then piece 10 at P_END with i + 1, s8c_close_cont).
   - Each arm is ONE run of the token engine (YC1fPx's paj_run_to_x at fx := fxc) from a closed symbolic state
     (ss10z, ss10v c, ss9 c; the branch outcome is a condition of the state) to its stop pc. Every instrumented check
     (a load of the shadow byte at (a >> 3) + 0x7fff8000 and a compare) continues on its good arm: its error path (a
     call of errpath_load1, _load4, _load8, _store4 or _store8) and its partial-granule arm are shown not taken by an
     addressability obligation on the entry memory: x0 + i (src_rd), q, q + 16, q + 32 (in's 40 bytes, s8c_q_ra),
     v' + 40 (prhex_tree's 56 bytes).
   - s8c_ZB, the ONE premise of the _zb lemmas: the per-byte zero-shadow law of the real stack, AR_laws_x's field
     alx_zshadow_byte (YCbqG.v 219748197d6b, :317). It gives the shadow of `in` on the caller's real stack; the
     journal cannot keep q's shadow (shadow_addr q ~ 0x1000_7fef_0000 < alloc_ceiling 0x7fff7f800000, so
     ajournal_xb's clause at YCbqG.v:357 does not cover it), and alx_zshadow's range form misses the granule
     [q + 32, q + 40) unless ly_stk_lo ly mod 8 = 0.
     ev_items_end_holds / ev_items_close_holds (the last lemmas of this file) cite it as
     `alx_zshadow_byte SEGS B ARx LAWS`: they hold under LAWS only.
   - MEMNORM (S8aIface.v's header): ev_mid's last conjunct `YAkMemnorm.memnorm SEGS mem` crosses each arm's run by
     YC1fPx's paj_run_to_x_inv at P := YAkMemnorm.memnorm SEGS (laws YSRrMemnorm.srr_inv_laws_memnorm_k SEGS);
     s8c_mid_frame, s8c_end_post and s8c_close_mid take it at the end memory. The pieces make no call.
   - Numerals. ADDRESS: none typed (pcs are ev_k / ev_pc of S8aIface's EV_* offsets over the generated A_prog_sigma /
     A_prog_base / pa_val). LENGTH: in's field offsets 0 8 16 24 32 36 40 and sizes 4 8, the node's n at 40 and its 56
     bytes, the spill slots 24 48 56 64 104 120 128 (s1-relative), chunk widths 1 4 8, the 8-byte shadow granule and
     its shift 3, 2 ^ 64 (word range), 2 ^ 47 (user address space), 2 ^ 44 (shadow span), 256 / 288 (the prologue's
     `addi sp, sp, -256; andi sp, sp, -32`). DERIVED: 2 ^ 47 - 40 / - 56 / - 64 (the space minus a struct, a node, a
     margin), 4096 (ESTACK, the floor of STK_ex_value; the lowest application address), Z.of_nat PjGrammar.MAXD (the
     depth bound), 152 / 248 (the extent of EV_SAVED), the engine's atom numbers 9 .. 34 (registers 0-31, extras
     from 32). WORD: 0, 1, -1 (18446744073709551615 = 2 ^ 64 - 1 as the register word), 93 / 125 (the closers),
     255 (a byte), 5 / 6 (the JArr / JObj tags).
   - #102 (the port to image A', a working branch on the cut 7cdbb61b5fa0): ported from the old-pin proof of
     a working branch 8f1571cb9e13 (image A d83eb25d, twin f0d2e8d4, ex_value 0x82f30) BY SYMBOL: every pc in
     a comment is A' ex_value 0x832a4 + the same offset (+0x374; checked against the A' listing of pin 1be0f53d, the
     stacknarrow neutral disassembly); the EV_* offsets and every stepped word are unchanged, so the runs need no edit.
     5 of the 51 words walked differ, all untaken report arms' `jal __asan_report_*`; the CHANGED frame string (+0xa8 /
     +0xc4; the 15:33Z #102 ruling) is outside them. The proofs changed in one place: the kit's prh_ledger carries
     #102's two cells g_most / g_own_ran_out (PRH_Base.v prh_glob / prh_most / prh_own, ev_act's ea_most / ea_own), so
     s8c_foot_rng takes `most own` and s8c_mid_frame keeps the two cells across the frame as it keeps the other five.
   - Build: the targeted route, the internal file zfb-targets.e5b8f1f4ec31aa52.sh with TARGETS = this file's
     and S8aOpen.v's .vo, PAU=pau-preset-102 (the 4 #102 pins; asan 1be0f53d), FACTS 8f3e7e1a07f1, at a pushed
     commit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== the symbolic states at the cuts (closed terms; vm_compute runs the engine over them) ======== *)

(* ex_value's entry as an offset from the listing's base (DERIVED: the generated A_prog_sigma / A_prog_base) *)
Definition EV_BASE : Z := A_prog_sigma AS_ex_value - A_prog_base.
Definition ev_k (off : Z) : Z := EV_BASE + off.
(* the shadow address of atom n + c, in the form the instrumented code computes it: ((n + c) >> 3) + s8 *)
Definition shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0).
(* s8 (atom 24) holds SHADOW_OFF; the shadow band is [SHADOW_OFF, SHADOW_OFF + 2 ^ 44) *)
Definition EV_Bx : sv := SOff 24 0.
Definition EV_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* atoms: 9 s1 (spills), 10 a0 (x0 + i), 18 s2 (the frame), 19 s3 (q), 23 s7 (v'), 24 s8; extra atoms from 32.
   piece 10: 32 = v'->n, 33 = in->depth (dep + 1), 34 = in->differs (dln). piece 9: 32 = the byte at x0 + i,
   33 = the closer, 34 = s1 + 120 (length acc - 1). *)
Definition r_sp10 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 64 0 0 [YP09.mkChunk 48 (CVal 8 (SOff 19 16)); YP09.mkChunk 56 (CVal 8 (shx 19 16))].
Definition r_qdep : YP09.region := YP09.mkRegion (Some 19%nat) 16 20 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 33 0))].
Definition r_qdl : YP09.region := YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 34 0))].
Definition r_vn : YP09.region := YP09.mkRegion (Some 23%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
Definition fa_bx : nat * afact := (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition fa_q : nat * afact := (19%nat, mkAF kHighMemBeg (2 ^ 47 - 40) 3).
Definition fa_v : nat * afact := (23%nat, mkAF 1 (2 ^ 47 - 56) 0).
(* in->depth inside a container: dep + 1 in [1, MAXD] (lw sign-extends it unchanged) *)
Definition fa_dep : nat * afact := (33%nat, mkAF 1 (Z.of_nat PjGrammar.MAXD) 0).
(* piece 10, v' = 0 (s7 is 0: the `beqz s7` at 0x83cf0 is taken) *)
Definition ss10z : sstate :=
  mkSS (ev_k EV_END) (sr_set sr_atoms 23%bv (SLit 0)) [r_sp10; r_qdep; r_qdl] None (mkFacts [fa_bx; fa_q; fa_dep] [] []).
(* piece 10, v' <> 0, with the outcome of `beq a1, a0` at 0x83d0c (n = v'->n or not) as a condition *)
Definition ss10v (c : branch_cond) : sstate :=
  mkSS (ev_k EV_END) sr_atoms [r_sp10; r_qdep; r_qdl; r_vn] None
    (mkFacts [fa_bx; fa_q; fa_v; fa_dep] [mkAC c (SOff 11 0) (SOff 32 0)] []).
Definition r_sp9 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 128 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 18 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 0));
    YP09.mkChunk 120 (CVal 8 (SOff 34 0))].
Definition r_txt : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition r_qp : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 10 0))].
Definition fa_p : nat * afact := (10%nat, mkAF 4096 (2 ^ 47 - 64) 0).
Definition fa_c : nat * afact := (32%nat, mkAF 0 255 0).
(* piece 9, with the outcome of `bne a1, a2` at 0x83cd0 (the byte against the closer) as a condition *)
Definition ss9 (c : branch_cond) : sstate :=
  mkSS (ev_k EV_CLOSE) (sr_set (sr_set sr_atoms 11%bv (shx 10 0)) 26%bv (shx 19 0)) [r_sp9; r_txt; r_qp] None
    (mkFacts [fa_bx; fa_q; fa_p; fa_c] [mkAC c (SOff 32 0) (SOff 33 0)] []).

(* ======== pure lemmas: bytes, shadow arithmetic, the differs bookkeeping ======== *)

Lemma s8c_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros j Hj. change 256 with (2 ^ 8). rewrite !YO0a.testbit_mod_pow2 by lia.
destruct (j <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
rewrite !Z.shiftr_spec by lia. rewrite !YO0a.testbit_mod_pow2 by lia.
replace (j + 8 * Z.of_nat k <? 8 * Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; nia).
replace (j + 8 * Z.of_nat k <? 64) with true by (symmetry; apply Z.ltb_lt; nia). reflexivity.
Qed.

Section bytes.
Variable segs : list Segment.
Lemma s8c_chunk_of_val : forall E m base off (w : N) e v, (w <= 8)%N -> sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (base + off) (N.to_nat w) v -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v Hw He Hv i Hi. unfold YP09.c_len, YP09.cv_len in Hi. cbn [YP09.c_val YP09.c_off] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
pose proof (Hv (Z.to_nat i) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. rewrite H.
f_equal. rewrite He. replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia. apply s8c_byte_eq; lia.
Qed.
Lemma s8c_val_of_chunk : forall E m base off (w : N) e, (w <= 8)%N ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)) -> val_mem segs m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros E m base off w e Hw Hc k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
pose proof (s8c_byte_eq (bv_unsigned (sv_denot E e)) (N.to_nat w) k Hk ltac:(lia)) as Hb.
rewrite Z_to_bv_bv_unsigned in Hb. symmetry. exact Hb.
Qed.
End bytes.

Lemma s8c_U_shx : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  ew E 24 = Z_to_bv 64 SHADOW_OFF -> sv_denot E (shx n c) = Z_to_bv 64 (shadow_addr (x + c)).
Proof.
intros E n c x Hn Hx Hxc H24. apply bv_eq.
change (bv_unsigned (sv_denot E (shx n c))) with (U E (shx n c)). unfold shx.
rewrite !U_SAlu, (U_atom_off E n x c Hn Hx Hxc), U_SLit, (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64, shadow_addr, SHADOW_OFF.
change (bv_modulus 64) with (2 ^ 64).
assert (0 <= (x + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the tree comparison (pure spec; COPIED from the released plain proof
   proofs/omx-clap-core/fuzz_preset/lib/Prog/ex_value_m.v:453-519, not Required, not cited) ---- *)
Lemma s8c_jv_eq_dec : forall a b : PjTree.jv, {a = b} + {a <> b}.
Proof.
  fix F 1. intros a b.
  destruct a as [| | |t1 c1|s1|l1|m1]; destruct b as [| | |t2 c2|s2|l2|m2];
    try (left; reflexivity); try (right; discriminate).
  - destruct (list_eq_dec Z.eq_dec t1 t2) as [<-|N]; [|right; congruence].
    destruct (Z.eq_dec c1 c2) as [<-|N]; [left; reflexivity|right; congruence].
  - destruct (list_eq_dec Z.eq_dec s1 s2) as [<-|N]; [left; reflexivity|right; congruence].
  - revert l2. revert l1. fix G 1.
    intros [|x l1] [|y l2]; [left; reflexivity|right; discriminate|right; discriminate|].
    destruct (F x y) as [<-|N]; [|right; congruence].
    destruct (G l1 l2) as [E|N]; [left; congruence|right; congruence].
  - revert m2. revert m1. fix G 1.
    intros [|[n1 u1] m1] [|[n2 u2] m2]; [left; reflexivity|right; discriminate|right; discriminate|].
    destruct (list_eq_dec Z.eq_dec n1 n2) as [<-|N]; [|right; congruence].
    destruct (F u1 u2) as [<-|N]; [|right; congruence].
    destruct (G m1 m2) as [E|N]; [left; congruence|right; congruence].
Qed.
Lemma s8c_list_neq_split : forall (A : Type) (dec : forall a b : A, {a = b} + {a <> b}) (d : A) (l1 l2 : list A),
  l1 <> l2 -> length l1 <> length l2 \/
  exists j, (j < length l1)%nat /\ (j < length l2)%nat /\ nth j l1 d <> nth j l2 d.
Proof.
  intros A dec d l1. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - exfalso. apply H. reflexivity.
  - left. cbn [length]. lia.
  - left. cbn [length]. lia.
  - destruct (dec x y) as [<-|Nxy].
    + assert (Hl : l1 <> l2) by congruence.
      destruct (IH l2 Hl) as [L|(j & J1 & J2 & J3)].
      * left. cbn [length]. lia.
      * right. exists (S j). cbn [length nth]. split; [lia|]. split; [lia|]. exact J3.
    + right. exists 0%nat. cbn [length nth]. split; [lia|]. split; [lia|]. exact Nxy.
Qed.
Lemma s8c_pair_dec : forall a b : list Z * PjTree.jv, {a = b} + {a <> b}.
Proof.
  intros [n1 u1] [n2 u2].
  destruct (list_eq_dec Z.eq_dec n1 n2) as [<-|N]; [|right; congruence].
  destruct (s8c_jv_eq_dec u1 u2) as [<-|N]; [left; reflexivity|right; congruence].
Qed.

(* ---- the differs bookkeeping at the end of a container (C :289-290), from ev_dl ---- *)
Lemma s8c_tag_mk : forall o l, PjTree.tag (PjGrammar.mk o l) = if o then 6 else 5.
Proof. intros [|] l; reflexivity. Qed.
Lemma s8c_kids_mk : forall o l, length (ev_kids (PjGrammar.mk o l)) = length l.
Proof. intros [|] l; cbn [PjGrammar.mk ev_kids]; [reflexivity | rewrite !length_map; reflexivity]. Qed.
Lemma s8c_v'_nz : forall v o t, ev_v' v o t <> 0 -> v <> 0 /\ PjTree.tag t = (if o then 6 else 5).
Proof.
  intros v o t H. unfold ev_v', ev_tv in H. destruct (Z.eqb_spec v 0) as [E|E]; [subst v; cbn in H; lia|].
  cbn [orb] in H. destruct (Z.eqb_spec (PjTree.tag t) (if o then 6 else 5)); [split; assumption | lia].
Qed.
Lemma s8c_bad_iff : forall (o : bool) (t : PjTree.jv) acc, PjTree.tag t = (if o then 6 else 5) -> length (ev_kids t) = length acc ->
  ((exists j, (j < length acc)%nat /\ ev_bad o t j (nth j (rev acc) ([], PjTree.JNull))) <->
   t <> PjGrammar.mk o (rev acc)).
Proof.
  intros o t acc Ht Hl. unfold ev_bad.
  destruct o; destruct t as [| | | | |ts|ms]; cbn [PjTree.tag] in Ht; try lia; cbn [ev_kids PjGrammar.mk] in *.
  - split.
    + intros (j & Hj & [Hb|[(_ & Hb)|Hb]]) E; injection E as E; subst ms; [lia | exact (Hb eq_refl) | exact (Hb eq_refl)].
    + intros Hn. assert (Hn' : ms <> rev acc) by congruence.
      destruct (s8c_list_neq_split _ s8c_pair_dec ([], PjTree.JNull) ms (rev acc) Hn') as [L|(j & J1 & J2 & J3)];
        [rewrite length_rev in L; lia|].
      exists j. split; [rewrite length_rev in J2; exact J2|]. right.
      revert J3. destruct (nth j ms ([], PjTree.JNull)) as [a u], (nth j (rev acc) ([], PjTree.JNull)) as [b w].
      cbn [fst snd]. intro J3.
      destruct (list_eq_dec Z.eq_dec a b) as [<-|N]; [right; congruence | left; split; [reflexivity | exact N]].
  - rewrite length_map in Hl.
    assert (Ek : forall j, snd (nth j (map (fun u => (@nil Z, u)) ts) ([], PjTree.JNull)) = nth j ts PjTree.JNull).
    { intros j. change ([], PjTree.JNull) with ((fun u : PjTree.jv => (@nil Z, u)) PjTree.JNull).
      rewrite map_nth. reflexivity. }
    assert (Ea : forall j, nth j (map snd (rev acc)) PjTree.JNull = snd (nth j (rev acc) ([], PjTree.JNull))).
    { intros j. change PjTree.JNull with (@snd (list Z) PjTree.jv ([], PjTree.JNull)) at 1. apply map_nth. }
    split.
    + intros (j & Hj & [Hb|[(Hf & _)|Hb]]) E; [rewrite length_map in Hb; lia | discriminate Hf |].
      injection E as E. rewrite Ek in Hb. apply Hb. rewrite E, Ea. reflexivity.
    + intros Hn. assert (Hn' : ts <> map snd (rev acc)) by congruence.
      destruct (s8c_list_neq_split _ s8c_jv_eq_dec PjTree.JNull ts (map snd (rev acc)) Hn') as [L|(j & J1 & J2 & J3)];
        [rewrite length_map, length_rev in L; lia|].
      exists j. split; [rewrite length_map, length_rev in J2; exact J2|]. right; right.
      rewrite Ek, <- Ea. exact J3.
Qed.
(* the differs outcome: dl' = dln when the count is not compared (v' = 0) or the machine's 64-bit compare finds it
   equal (then v'->n <= length acc: a longer acc already holds a bad item), dl' = 1 when it differs *)
Lemma s8c_dl_keep : forall dl0 v o t acc dln,
  ev_dl dl0 v o t acc dln -> (ev_v' v o t = 0 \/ (length (ev_kids t) <= length acc)%nat) ->
  (dln = 0 \/ dln = 1) /\ (dln = 1 <-> dl0 = 1 \/ (v <> 0 /\ t <> PjGrammar.mk o (rev acc))).
Proof.
  intros dl0 v o t acc dln (H01 & Hiff) Hc. split; [exact H01|]. rewrite Hiff.
  destruct (Z.eq_dec v 0) as [E|Ev]; [subst v; split; intros [H|H]; auto; destruct H as [H _]; exfalso; apply H; reflexivity|].
  destruct (ev_tv v o t) eqn:Etv.
  - assert (Ht : PjTree.tag t = (if o then 6 else 5)).
    { unfold ev_tv in Etv. apply orb_prop in Etv as [E|E]; apply Z.eqb_eq in E; [lia | exact E]. }
    assert (Hle : (length (ev_kids t) <= length acc)%nat).
    { destruct Hc as [Hz|Hl]; [|exact Hl]. exfalso. unfold ev_v' in Hz. rewrite Etv in Hz. exact (Ev Hz). }
    destruct (Nat.eq_dec (length (ev_kids t)) (length acc)) as [Hl|Hl].
    + rewrite <- (s8c_bad_iff o t acc Ht Hl).
      split; intros [H|H]; auto; right; [destruct H as [_ [H|H]]; [discriminate | split; assumption] |
        destruct H as [_ H]; split; [exact Ev | right; exact H]].
    + split; intros _; right; split; try exact Ev.
      * intros E. apply Hl. rewrite E, s8c_kids_mk, length_rev. reflexivity.
      * right. exists (length (ev_kids t)). split; [lia|]. left. lia.
  - assert (Ht : PjTree.tag t <> (if o then 6 else 5)).
    { unfold ev_tv in Etv. apply orb_false_iff in Etv as [_ E]. apply Z.eqb_neq. exact E. }
    split; intros _; right; split; [exact Ev| | exact Ev | left; reflexivity].
    intros E. apply Ht. rewrite E. apply s8c_tag_mk.
Qed.
Lemma s8c_dl_set : forall dl0 v o t acc,
  ev_v' v o t <> 0 -> length (ev_kids t) <> length acc ->
  (1 = 0 \/ 1 = 1) /\ (1 = 1 <-> dl0 = 1 \/ (v <> 0 /\ t <> PjGrammar.mk o (rev acc))).
Proof.
  intros dl0 v o t acc Hv Hl. destruct (s8c_v'_nz v o t Hv) as [Ev _].
  split; [right; reflexivity|]. split; [intros _; right; split; [exact Ev|] | reflexivity].
  intros E. apply Hl. rewrite E, s8c_kids_mk, length_rev. reflexivity.
Qed.

(* ---- every block of a tree's footprint is one of lblk's (it bounds the footprint by the harness blocks) ---- *)
Section pjl.
Variable segs : list Segment.
Lemma s8c_items_in : forall P a l D, PRH_Reader.pj_itemsR P a l D -> forall b, In b D ->
  exists a' u D1, In u l /\ P a' u D1 /\ In b D1.
Proof.
intros P a l. revert a. induction l as [|u r IH]; intros a D H b Hb; cbn [PRH_Reader.pj_itemsR] in H;
  [subst D; destruct Hb|].
destruct H as (D1 & D2 & -> & HP & Hr). apply in_app_or in Hb as [Hb|Hb].
- exists a, u, D1. split; [left; reflexivity|]. split; assumption.
- destruct (IH (a + 56) D2 Hr b Hb) as (a' & u' & D1' & Hu & HP' & Hb').
  exists a', u', D1'. split; [right; exact Hu|]. split; assumption.
Qed.
Lemma s8c_mems_in : forall m lblk P a ka l D, PRH_Reader.pj_memsR segs m lblk P a ka l D -> forall b, In b D ->
  lblk (fst b) (snd b) \/ exists a' u D1, In u (map snd l) /\ P a' u D1 /\ In b D1.
Proof.
intros m lblk P a ka l. revert a ka. induction l as [|[nm u] r IH]; intros a ka D H b Hb;
  cbn [PRH_Reader.pj_memsR] in H; [subst D; destruct Hb|].
destruct H as (x & k & D1 & D2 & -> & _ & Hcs & HP & Hr). destruct Hb as [<-|Hb].
- left. exact (proj1 Hcs).
- apply in_app_or in Hb as [Hb|Hb].
  + right. exists a, u, D1. split; [left; reflexivity|]. split; assumption.
  + destruct (IH (a + 56) (ka + 8) D2 Hr b Hb) as [L|(a' & u' & D1' & Hu & HP' & Hb')]; [left; exact L|].
    right. exists a', u', D1'. split; [right; exact Hu|]. split; assumption.
Qed.
Lemma s8c_pj_lblk : forall t m lblk p D, PRH_Reader.pj_nodeR segs m lblk p t D -> forall b, In b D ->
  lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk p D H b Hb; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb');
  try (destruct Hb' as (_ & _ & _ & _ & _ & ->); destruct Hb).
- destruct Hb' as (_ & _ & _ & _ & _ & k & Hc & ->). destruct Hb as [<-|[]]. exact (proj1 Hc).
- destruct Hb' as (_ & _ & _ & _ & k & Hc & ->). destruct Hb as [<-|[]]. exact (proj1 Hc).
- destruct Hb' as (_ & _ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (Z.eqb_spec cap 0) as [E|E]; [destruct Hb|]. destruct Hb as [<-|[]].
    destruct Hcap as [(Hc & _)|(_ & L)]; [lia | exact L].
  + destruct (s8c_items_in _ _ _ _ Hi b Hb) as (a' & u & D1 & Hu & HP & Hb1).
    rewrite Forall_forall in IH. exact (IH u Hu m lblk a' D1 HP b Hb1).
- destruct Hb' as (_ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (Z.eqb_spec cap 0) as [E|E]; [destruct Hb|].
    destruct Hcap as [(Hc & _)|(_ & L1 & L2)]; [lia|]. destruct Hb as [<-|[<-|[]]]; assumption.
  + destruct (s8c_mems_in _ _ _ _ _ _ _ Hi b Hb) as [L|(a' & u & D1 & Hu & HP & Hb1)]; [exact L|].
    rewrite Forall_forall in IH. apply in_map_iff in Hu as ([nm u'] & <- & Hu).
    exact (IH (nm, u') Hu m lblk a' D1 HP b Hb1).
Qed.
(* the node's item count (pj_hdrR's n at p + 40) *)
Lemma s8c_pj_n : forall m lblk p t D, PRH_Reader.pj_nodeR segs m lblk p t D -> (PjTree.tag t = 5 \/ PjTree.tag t = 6) ->
  val_mem segs m (p + 40) 8 (Z.of_nat (length (ev_kids t))) /\ Z.of_nat (length (ev_kids t)) < 2 ^ 64.
Proof.
intros m lblk p t D H Ht. destruct t as [| | | | |ts|ms]; cbn [PjTree.tag] in Ht; try lia;
  cbn [PRH_Reader.pj_nodeR ev_kids] in H |- *; destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb);
  destruct Hh as (_ & _ & _ & _ & _ & _ & (Hnr & Hn) & _).
- destruct Hb as (_ & _ & En & _). rewrite length_map, <- En. split; [exact Hn | exact (proj2 Hnr)].
- destruct Hb as (_ & En & _). rewrite <- En. split; [exact Hn | exact (proj2 Hnr)].
Qed.
End pjl.

(* ======== the memory frame: pieces 9 / 10 write only in's fields p (q), depth (q + 16), differs (q + 32) ======== *)
Definition qw (q a : Z) : Prop := q <= a < q + 8 \/ q + 16 <= a < q + 20 \/ q + 32 <= a < q + 36.
Definition mframe (q : Z) (mem mem' : word -> option byte) : Prop :=
  (0 <= q /\ q + 40 <= 2 ^ 64) /\ forall x : word, ~ qw q (bv_unsigned x) -> mem' x = mem x.

Section frame.
Variable segs : list Segment.
Variables (q : Z) (mem mem' : word -> option byte).
Hypothesis HF : mframe q mem mem'.
Lemma s8c_mr : forall (H : word -> bool) z, 0 <= z < 2 ^ 64 -> ~ qw q z ->
  mrestrict H mem' (Z_to_bv 64 z) = mrestrict H mem (Z_to_bv 64 z).
Proof.
intros H z Hz Hq. unfold mrestrict. destruct (H (Z_to_bv 64 z)); [reflexivity|]. apply (proj2 HF).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hq.
Qed.
Lemma s8c_mbyte : forall (H : word -> bool) z, 0 <= z < 2 ^ 64 -> ~ qw q z ->
  YP09.mbyte segs (mrestrict H mem') z = YP09.mbyte segs (mrestrict H mem) z.
Proof. intros H z Hz Hq. unfold YP09.mbyte. rewrite (s8c_mr H z Hz Hq). reflexivity. Qed.
Lemma s8c_aview : forall (H : word -> bool) z, 0 <= z < 2 ^ 64 -> ~ qw q z -> aview segs H mem' z = aview segs H mem z.
Proof. intros H z Hz Hq. unfold aview. rewrite (s8c_mbyte H z Hz Hq). reflexivity. Qed.
Lemma s8c_val : forall (H : word -> bool) a (n : nat) v, 0 <= a -> a + Z.of_nat n <= q ->
  val_mem segs (mrestrict H mem) a n v -> val_mem segs (mrestrict H mem') a n v.
Proof.
intros H a n v Ha Hn Hv k Hk. pose proof (proj1 HF). rewrite s8c_mbyte; [exact (Hv k Hk) | |]; unfold qw; lia.
Qed.
Lemma s8c_val_hi : forall (H : word -> bool) a (n : nat) v, q + 40 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem segs (mrestrict H mem) a n v -> val_mem segs (mrestrict H mem') a n v.
Proof.
intros H a n v Ha Hn Hv k Hk. pose proof (proj1 HF). rewrite s8c_mbyte; [exact (Hv k Hk) | |]; unfold qw; lia.
Qed.
Lemma s8c_val_in : forall (H : word -> bool) a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat n -> ~ qw q z) ->
  val_mem segs (mrestrict H mem) a n v -> val_mem segs (mrestrict H mem') a n v.
Proof.
intros H a n v Ha Hn Hq Hv k Hk. rewrite s8c_mbyte; [exact (Hv k Hk) | lia | apply Hq; lia].
Qed.
(* shadow facts of bytes below 2 ^ 47: their shadow bytes lie below SHADOW_OFF + 2 ^ 44 + 8 <= q *)
Lemma s8c_ra : forall (H : word -> bool) a n, SHADOW_OFF + 2 ^ 44 + 8 <= q -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview segs H mem) SHADOW_OFF a n -> range_addressable (aview segs H mem') SHADOW_OFF a n.
Proof.
intros H a n Hq Ha Hn Hr. apply (range_addressable_agree (aview segs H mem)); [|exact Hr].
intros x Hx. unfold shadow_of_addr. assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
pose proof (proj1 HF). apply s8c_aview; unfold qw, SHADOW_OFF in *; lia.
Qed.
Lemma s8c_hull : forall (H : word -> bool) a n, SHADOW_OFF + 2 ^ 44 + 8 <= q -> 0 <= a -> 0 < n -> a + n <= 2 ^ 47 ->
  shadow_hull_vis (aview segs H mem) a n -> shadow_hull_vis (aview segs H mem') a n.
Proof.
intros H a n Hq Ha Hn Han Hh s Hs. pose proof (proj1 HF). rewrite s8c_aview; [exact (Hh s Hs) | |];
unfold shadow_addr in Hs; assert (0 <= (a + n - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
assert (0 <= a / 8) by (apply Z.div_pos; lia);
assert ((SHADOW_OFF + a / 8) / 8 * 8 >= 0) by (unfold SHADOW_OFF; pose proof (Z.div_pos (2147450880 + a / 8) 8); lia);
assert ((SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8)
  by (pose proof (Z.mul_div_le (SHADOW_OFF + (a + n - 1) / 8) 8); lia);
unfold qw, SHADOW_OFF in *; lia.
Qed.
Lemma s8c_wr : forall (H : word -> bool) a, 0 <= a < 2 ^ 64 -> ~ qw q a ->
  writable_at segs (mrestrict H mem) a -> writable_at segs (mrestrict H mem') a.
Proof. intros H a Ha Hq Hw. unfold writable_at, wview in *. rewrite (s8c_mr H a Ha Hq). exact Hw. Qed.
Lemma s8c_garr8 : forall (H : word -> bool) p l, 0 <= p -> p + Z.of_nat (length l) <= q ->
  garr8 segs (mrestrict H mem) p l -> garr8 segs (mrestrict H mem') p l.
Proof.
intros H p l Hp Hl Hg j Hj. destruct (Hg j Hj) as [V R]. split; [|exact R].
apply (s8c_val H); [lia | lia | exact V].
Qed.
Lemma s8c_rdword : forall (H : word -> bool) a, 0 <= a -> a + 8 <= q ->
  rdword (aview segs H mem') a = rdword (aview segs H mem) a.
Proof.
intros H a Ha Hq. unfold rdword. pose proof (proj1 HF).
rewrite !s8c_aview by (unfold qw; lia). reflexivity.
Qed.
End frame.
Lemma s8c_val_C : forall segs (C : Z -> Prop) (mem mem' : word -> option byte) (H : word -> bool) a (n : nat) v,
  (forall x : word, ~ C (bv_unsigned x) -> mem' x = mem x) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat n -> ~ C z) ->
  val_mem segs (mrestrict H mem) a n v -> val_mem segs (mrestrict H mem') a n v.
Proof.
intros segs C mem mem' H a n v HF Ha Hn HC Hv k Hk.
assert (E : YP09.mbyte segs (mrestrict H mem') (a + Z.of_nat k) = YP09.mbyte segs (mrestrict H mem) (a + Z.of_nat k)).
{ unfold YP09.mbyte, mrestrict. destruct (H (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
  rewrite HF; [reflexivity|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. apply HC. lia. }
rewrite E. exact (Hv k Hk).
Qed.
(* a word-level keep of every byte of X, and X inside [0, 2 ^ 64), is PRH_Reader's agreement on X (pj_nodeR_frame's
   premise): the same byte, and a writable byte stays writable *)
Lemma s8c_agree : forall segs (H : word -> bool) (mem mem' : word -> option byte) (X : Z -> Prop),
  (forall x : word, X (bv_unsigned x) -> mem' x = mem x) -> (forall x, X x -> 0 <= x < 2 ^ 64) ->
  PRH_Reader.pj_agreeR segs (mrestrict H mem) (mrestrict H mem') X.
Proof.
intros segs H mem mem' X HK HR x HX.
assert (E : mrestrict H mem' (Z_to_bv 64 x) = mrestrict H mem (Z_to_bv 64 x)).
{ unfold mrestrict. destruct (H (Z_to_bv 64 x)); [reflexivity|]. apply HK.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by exact (HR x HX). exact HX. }
split.
- unfold YP09.mbyte. rewrite E. reflexivity.
- unfold writable_at, wview. rewrite E. exact (fun h => h).
Qed.

(* ======== the pieces, at L := A_prog_listing, PA := PI_prog_A, PI := prh_img_A, cp := CfParams_preset ======== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
#[local] Notation EVPRE := (@ev_pre fx rc CfParams_preset prh_img_A A_prog_listing PI_prog_A B ARx).
#[local] Notation EVMID := (@ev_mid rc CfParams_preset prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* what the pieces use of ev_pre: the caller's window inside the stack band, below 2 ^ 47 *)
Lemma s8c_pre_q : forall a, EVPRE a ->
  alloc_ceiling + 4096 <= ea_sp0 a /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\
  ea_sp0 a + ea_d a <= ly_stk_hi (ea_ly a) /\ ly_stk_hi (ea_ly a) <= 2 ^ 47 /\ ly_stk_lo (ea_ly a) <= ea_sp0 a /\
  ea_q a mod 8 = 0 /\ 0 <= ea_d a /\ 4096 <= ea_STK (PI := prh_img_A) a.
Proof.
intros a H. unfold ev_pre in H. cbv zeta in H.
destruct H as ((HPRE & _) & _ & _ & _ & _ & _ & Hq8 & _ & Hq1 & Hq2 & Hfw & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HS0 & Hlo & HloS & Hhi & H47 & _ & Htop & Htop2).
destruct Hfw as (Hd0 & _ & Hdtop & _).
assert (HSTK : 4096 <= ea_STK a).
{ unfold ea_STK, STK_ex_value. pose proof (Zle_0_nat (S (ea_n a))).
  match goal with |- context [zmaxl ?l] => let v := eval vm_compute in (zmaxl l) in change (zmaxl l) with v end.
  match goal with |- context [@pi_frame ?P ?f] => let v := eval vm_compute in (@pi_frame P f) in
    change (@pi_frame P f) with v end. lia. }
unfold ea_sp0. repeat split; lia.
Qed.

(* the journal's facts the frame needs: the current allocator relation, the layout, the own frame *)
Lemma s8c_mid_bounds : forall a ly S Hp W mem md k p dep dl, EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  ARx ly S Hp W mem md /\ ly_stk_hi ly = ly_stk_hi (ea_ly a) /\ ly_stk_lo ly = ly_stk_lo (ea_ly a) /\
  ea_fr a = frame_addr ly 1 (ea_pos a) /\ In (1, ea_pos a) (frames S).
Proof.
intros a ly S Hp W mem md k p dep dl _ (HJ & _).
destruct HJ as (HAR & Hly & _ & _ & _ & Hfr & _).
destruct Hly as (_ & _ & _ & _ & _ & HF & _ & _ & _ & Hlo & Hhi & _).
split; [exact HAR|]. split; [exact Hhi|]. split; [exact Hlo|]. split.
- unfold ea_fr, frame_addr. rewrite HF. reflexivity.
- rewrite Hfr. left. reflexivity.
Qed.

(* a tree's footprint lies below 2 ^ 47: its root by the premise, every other block of it is a live harness block
   (s8c_pj_lblk), inside an allocator block below alloc_ceiling (alx_blocks) *)
Lemma s8c_foot_rng : forall ly S Hp W mem md Lam peak cnt fail ran most own m p t D,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_Reader.pj_nodeR SEGS m (prh_lin Lam) p t D -> 0 <= p -> p + 56 <= 2 ^ 47 ->
  forall x, PRH_Reader.pj_footR p D x -> 0 <= x < 2 ^ 47.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own m p t D HAR HL Hpj Hp0 Hp1 x [Hx | ([b k] & Hin & Hx)]; [lia|].
pose proof asan_consts as (C1 & _).
pose proof (s8c_pj_lblk SEGS _ _ _ _ _ Hpj (b, k) Hin) as Hl. cbn [fst snd] in Hl. unfold prh_lin in Hl.
destruct HL as (_ & _ & Hhb & _). rewrite Forall_forall in Hhb.
destruct (Hhb (b, k) Hl) as (Hk0 & Hab & _). cbn [fst snd] in *. change (@cf_head CfParams_preset) with 16 in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
unfold PRH_Reader.pj_holdsR in Hx. cbn [fst snd] in Hx.
unfold req_size in Hc. destruct (Z.eqb_spec (k + 16) 0); lia.
Qed.

(* EV_MID survives a change of in's three written fields: everything else ev_mid reads lies below q (the text,
   the scratch, the tree, the ledger, the save area, the frame's flag word, all their shadow bytes), or is a byte
   of [sp0, sp0 + d) outside FP, which the change misses. *)
Lemma s8c_mid_frame : forall a ly S Hp W mem md k p dep dl mem' md' p' dep' dl',
  EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK (PI := prh_img_A) a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  mframe (ea_q a) mem mem' ->
  prhex_cur W mem' (ea_q a) p' (ea_x0 a + ea_len a) dep' (ea_scr a) dl' ->
  YAkMemnorm.memnorm SEGS mem' ->
  EVMID a ly S Hp W mem' md' k p' dep' dl'.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' p' dep' dl' HPRE HMID HJ' HF Hcur' HMN'.
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
destruct (s8c_mid_bounds a ly S Hp W mem md k p dep dl HPRE HMID) as (HAR & Ehi & Elo & Efr & Hin1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HQ : 0 <= ea_q a /\ ea_q a + 40 <= 2 ^ 64) by lia.
assert (HQs : SHADOW_OFF + 2 ^ 44 + 8 <= ea_q a) by (unfold SHADOW_OFF; lia).
pose proof HPRE as HPRE'. unfold ev_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hscq & Hvt & _).
destruct HMID as (HJ & Hwin & HHp & Hbl & HL & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & Hrl & Hrp & _).
split; [exact HJ'|]. split.
{ intros z Hz Hnf. rewrite (s8c_aview SEGS (ea_q a) mem mem' HF); [exact (Hwin z Hz Hnf) | lia |].
  intros Hqw. apply Hnf. unfold ea_FP. destruct Hqw as [Hw|[Hw|Hw]];
  [exists (ea_q a, ea_q a + 8) | exists (ea_q a + 16, ea_q a + 20) | exists (ea_q a + 32, ea_q a + 36)];
  (split; [cbn; tauto | cbn [fst snd]; lia]). }
split; [exact HHp|]. split; [exact Hbl|]. split.
{ (* the ledger: alloc.c's statics (image addresses) and the harness blocks' heads, all below alloc_ceiling *)
  (* #102: prh_glob carries g_most / g_own_ran_out (PRH_Base.v prh_most / prh_own), kept as the five are *)
  unfold prh_ledger, prh_glob, prh_most, prh_own in HL |- *.
  destruct HL as ((G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Gr) & Hnd & Hhb & Hperm).
  assert (Hpi : forall z, z = @pi_g_live prh_img_A \/ z = @pi_g_peak prh_img_A \/ z = @pi_g_count prh_img_A \/
      z = @pi_g_fail prh_img_A \/ z = @pi_g_ran_out prh_img_A \/ z = @pi_g_most prh_img_A \/
      z = @pi_g_own_ran_out prh_img_A -> 0 <= z /\ z + 8 <= ea_q a).
  { intros z Hz. repeat destruct Hz as [Hz|Hz]; subst z; vm_compute pi_g_live; vm_compute pi_g_peak;
    vm_compute pi_g_count; vm_compute pi_g_fail; vm_compute pi_g_ran_out; vm_compute pi_g_most;
    vm_compute pi_g_own_ran_out; lia. }
  split; [|split; [exact Hnd|split; [|exact Hperm]]].
  - split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_live prh_img_A) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G1];
       pose proof (Hpi _ (or_introl eq_refl)); lia|].
    split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_peak prh_img_A) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G2];
       pose proof (Hpi _ (or_intror (or_introl eq_refl))); lia|].
    split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_count prh_img_A) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G3];
       pose proof (Hpi _ (or_intror (or_intror (or_introl eq_refl)))); lia|].
    split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_fail prh_img_A) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G4];
       pose proof (Hpi _ (or_intror (or_intror (or_intror (or_introl eq_refl))))); lia|].
    split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_ran_out prh_img_A) with 1%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G5];
       pose proof (Hpi _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))); lia|].
    split; [split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_most prh_img_A) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G6];
       pose proof (Hpi _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))); lia
       | exact G6r]|].
    split; [split; [apply (s8c_val SEGS (ea_q a) mem mem' HF);
       [|change (@pi_gz_own_ran_out prh_img_A) with 1%nat; cbn [Z.of_nat Pos.of_succ_nat]|exact G7];
       pose proof (Hpi _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror eq_refl))))))); lia
       | exact G7r]|].
    exact Gr.
  - eapply Forall_impl; [|exact Hhb]. intros [b m] (Hm0 & Hab & Hhp & Hb16 & Hv). cbn [fst snd] in *.
    split; [exact Hm0|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Hb16|].
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
    change (@cf_head CfParams_preset) with 16 in *.
    assert (16 <= req_size (m + 16)) by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
    apply (s8c_val SEGS (ea_q a) mem mem' HF); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | exact Hv]. }
split; [exact Hcur'|]. split.
{ destruct Hsrc as (Hb & H4 & Hc & Ham & Hra & Hhu). pose proof (Zle_0_nat (length (ea_x a))).
  split; [apply (s8c_garr8 SEGS (ea_q a) mem mem' HF); [lia | lia | exact Hb]|].
  split; [exact H4|]. split; [exact Hc|]. split; [exact Ham|]. split.
  - apply (s8c_ra SEGS (ea_q a) mem mem' HF); [lia | lia | lia | exact Hra].
  - intros Hn. apply (s8c_hull SEGS (ea_q a) mem mem' HF); [lia | lia | lia | lia | exact (Hhu Hn)]. }
split.
{ destruct Hwd as (H0 & Hc & Ham & Hw & Hra & Hhu). unfold ea_len in *. pose proof (Zle_0_nat (length (ea_x a))).
  split; [exact H0|]. split; [exact Hc|]. split; [exact Ham|]. split.
  - intros z Hz. destruct (Hw z Hz) as (Hwr & Ho & Hs). split; [|split; assumption].
    apply (s8c_wr SEGS (ea_q a) mem mem' HF); [lia | unfold qw; lia | exact Hwr].
  - split; [apply (s8c_ra SEGS (ea_q a) mem mem' HF); [lia | lia | lia | exact Hra]|].
    intros Hn. apply (s8c_hull SEGS (ea_q a) mem mem' HF); [lia | lia | lia | lia | exact (Hhu Hn)]. }
split.
{ destruct Hvt as [Hv0|(_ & _ & Hfoot)]; [left; exact Hv0|].
  destruct Htree as [Hv0|(Hpj & Hhome & Hra & Hhull)]; [left; exact Hv0|right].
  (* the root's home: a harness block, a fake frame (both below alloc_ceiling), or the stack below ly_stk_hi *)
  assert (Hvb : 0 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47).
  { destruct Hhome as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
    - destruct HL as (_ & _ & Hhb & _). rewrite Forall_forall in Hhb.
      destruct (Hhb (b, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in *. change (@cf_head CfParams_preset) with 16 in *.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
      unfold req_size in Hc. destruct (Z.eqb_spec (m + 16) 0); lia.
    - destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _).
      unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. lia.
    - unfold ea_sp0 in Hsp. lia. }
  split; [|split; [exact Hhome|split]].
  - apply (PRH_Reader.pj_nodeR_frame SEGS (ea_t a) (rdW W mem) (rdW W mem') (prh_lin (ea_Lam a)) (ea_v a) (ea_D a) Hpj).
    apply (s8c_agree SEGS (w_H W) mem mem').
    + intros x Hx. destruct (Hfoot _ Hx) as (_ & Hnq & _). apply (proj2 HF). unfold qw. lia.
    + intros x Hx.
      pose proof (s8c_foot_rng ly S Hp W mem md _ _ _ _ _ _ _ _ _ _ _ HAR HL Hpj (proj1 Hvb) (proj2 Hvb) x Hx). lia.
  - apply (s8c_ra SEGS (ea_q a) mem mem' HF); [lia | lia | lia | exact Hra].
  - apply (s8c_hull SEGS (ea_q a) mem mem' HF); [lia | lia | lia | lia | exact Hhull]. }
split.
{ unfold ev_saved in *. rewrite Forall_forall in *. intros orr Hin.
  assert (Ho : 152 <= fst orr <= 248)
    by (unfold EV_SAVED in Hin; repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]); destruct Hin).
  apply (s8c_val SEGS (ea_q a) mem mem' HF); [unfold ea_SA; lia | unfold ea_SA; cbn [Z.of_nat Pos.of_succ_nat]; lia |
    exact (Hsav orr Hin)]. }
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HAR Hin1) as (_ & Happ & _).
rewrite <- Efr in Happ. change (fs_frame_bytes 1) with 128 in *. unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hrl | split; [exact Hrp | exact HMN']]].
rewrite (s8c_rdword SEGS (ea_q a) mem mem' HF); [exact Hflag | lia | lia].
Qed.

(* ---- the shadow of in (q, on the caller's real stack): the per-byte zero-shadow law of the stack band
   (AR_laws_x's field alx_zshadow_byte: the ONE extra premise of the _zb lemmas, ZB). The journal cannot keep q's
   shadow: shadow_addr q is below alloc_ceiling, outside ajournal_xb's clause (YCbqG.v:357). ---- *)
Definition s8c_ZB : Prop := forall ly S Hp W mem md a, ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
  aview SEGS (w_H W) mem (SHADOW_OFF + a / 8) = Some 0.
Lemma s8c_q_ra : s8c_ZB -> forall a ly S Hp W mem md k p dep dl, EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_q a) 40.
Proof.
intros ZB a ly S Hp W mem md k p dep dl HPRE HMID.
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
destruct (s8c_mid_bounds a ly S Hp W mem md k p dep dl HPRE HMID) as (HAR & Ehi & Elo & _).
intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
apply (ZB ly S Hp W mem md x HAR). rewrite Elo, Ehi. lia.
Qed.

#[local] Notation EVEND := (@ev_at_end rc CfParams_preset prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
#[local] Notation EVEXIT := (@ev_to_exit fx rc CfParams_preset prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
(* the registers pieces 9 / 10 leave as they found them (beyond ev_regs: s6 = the frame) *)
Definition s8c_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv.

(* P_EXIT after piece 10: depth back to dep, differs dl', s11 = 0, the cursor where P_END left it *)
Lemma s8c_end_post : forall a fxc W regs mem md ly S Hp k o acc i dln regs' mem' md' dl',
  EVPRE a -> @ev_fx fx fxc -> EVEND a W regs mem md ly S Hp k o acc i dln ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  YAkMemnorm.memnorm SEGS mem' ->
  (forall x : word, ~ (ea_q a + 16 <= bv_unsigned x < ea_q a + 20 \/ ea_q a + 32 <= bv_unsigned x < ea_q a + 36) ->
     mem' x = mem x) ->
  val_mem SEGS (rdW W mem') (ea_q a + 16) 4 (ea_dep a) ->
  val_mem SEGS (rdW W mem') (ea_q a + 32) 4 dl' ->
  (dl' = 0 \/ dl' = 1) /\ (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> PjGrammar.mk o (rev acc))) ->
  (forall r, In r s8c_kept -> getr regs' r = getr regs r) -> getr regs' 27 = w64 0 ->
  EVEXIT a W (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc regs' EV_EXIT mem' md').
Proof.
intros a fxc W regs mem md ly S Hp k o acc i dln regs' mem' md' dl' HPRE HFX HEND HJ' HMN' HF Hdep Hdl Hdlo Hkept H27.
destruct HEND as (HMID & Hregs & H22 & H23 & H11 & Hs48 & Hs56 & Hdep31 & Hi & HV & Hdl0).
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HQ : 0 <= ea_q a /\ ea_q a + 40 <= 2 ^ 64) by lia.
exists fxc, regs', mem', md', ly, S, Hp, k, 0, (Z.of_nat i), (ea_dep a), dl'.
split; [reflexivity|]. split; [exact HFX|].
pose proof HMID as (_ & _ & _ & _ & _ & Hcur & _).
destruct Hcur as (P0 & P8 & P16 & P24 & P32).
pose (C := fun z => ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36).
split; [|split; [|split; [|split]]].
- apply (s8c_mid_frame a ly S Hp W mem md k _ _ _ mem' md' _ _ _ HPRE HMID HJ').
  + split; [exact HQ|]. intros x Hx. apply HF. intros Hc. apply Hx. unfold qw. lia.
  + split; [|split; [|split; [exact Hdep|split; [|exact Hdl]]]].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P0].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P8].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P24].
  + exact HMN'.
- unfold ev_regs in *. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
  repeat split; rewrite Hkept by (cbv; tauto); assumption.
- rewrite Hkept by (cbv; tauto). exact H22.
- exact H27.
- unfold ev_out. rewrite HV. split; [exact (proj1 Hdlo)|]. split; [reflexivity|].
  split; [rewrite length_skipn; unfold ea_len; lia|]. split; [reflexivity|]. exact (proj2 Hdlo).
Qed.

(* the tree's root lies below 2 ^ 47: its home is a harness block, a fake frame, or the stack below ly_stk_hi *)
Lemma s8c_v_bound : forall a ly S Hp W mem md k p dep dl, EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  ea_v a <> 0 -> 0 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47.
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID Hv.
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
destruct (s8c_mid_bounds a ly S Hp W mem md k p dep dl HPRE HMID) as (HAR & Ehi & Elo & Efr & Hin1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HMID as (_ & _ & _ & _ & HL & _ & _ & _ & Htree & _).
destruct Htree as [E0|(_ & Hhome & _)]; [contradiction|].
destruct Hhome as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- destruct HL as (_ & _ & Hhb & _). rewrite Forall_forall in Hhb.
  destruct (Hhb (b, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in *. change (@cf_head CfParams_preset) with 16 in *.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
  unfold req_size in Hc. destruct (Z.eqb_spec (m + 16) 0); lia.
- destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _).
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ. lia.
- unfold ea_sp0 in Hsp. lia.
Qed.

#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
(* the environment of piece 10: the registers, then v'->n, in->depth, in->differs *)
Definition s8c_E10 (regs : bvmap 5 word) (nv dep1 dln : Z) : env := Eimg (Ereg regs [w64 nv; w64 dep1; w64 dln]).
Lemma s8c_E10_reg : forall regs nv dep1 dln (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (s8c_E10 regs nv dep1 dln) n = getr regs r.
Proof. intros regs nv dep1 dln n r Hn Hr. unfold s8c_E10. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma s8c_E10_x : forall regs nv dep1 dln,
  ew (s8c_E10 regs nv dep1 dln) 32 = w64 nv /\ ew (s8c_E10 regs nv dep1 dln) 33 = w64 dep1 /\
  ew (s8c_E10 regs nv dep1 dln) 34 = w64 dln.
Proof.
intros. unfold s8c_E10. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 0)|]. split; [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)].
Qed.

(* the cut state of piece 10 with v' <> 0, the comparison n = v'->n assumed as the condition c *)
Lemma s8c_st10v : forall c a W regs mem md ly S Hp k o acc i dln fxc,
  EVPRE a -> EVEND a W regs mem md ly S Hp k o acc i dln -> ev_v' (ea_v a) o (ea_t a) <> 0 ->
  branch_taken c (w64 (Z.of_nat (length acc))) (w64 (Z.of_nat (length (ev_kids (ea_t a))))) = true ->
  @st_ok_pi SEGS VAL fxc (s8c_E10 regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) (ss10v c)
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (VAL A_TEXT + ev_k EV_END)) mem (seg_rom SEGS))).
Proof.
intros c a W regs mem md ly S Hp k o acc i dln fxc HPRE HEND Hv' Hc.
destruct HEND as (HMID & Hregs & H22 & H23 & H11 & Hs48 & Hs56 & Hdep31 & Hi & HV & Hdl0).
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s8c_v'_nz _ _ _ Hv') as [Hv0 Htag].
pose proof (s8c_v_bound _ _ _ _ _ _ _ _ _ _ _ HPRE HMID Hv0) as Hvb.
assert (Ev' : ev_v' (ea_v a) o (ea_t a) = ea_v a).
{ unfold ev_v', ev_tv. rewrite Htag, Z.eqb_refl, orb_true_r. reflexivity. }
rewrite Ev' in H23.
pose proof HMID as (HJ & _ & _ & _ & HL & Hcur & _ & _ & Htree & _).
destruct Htree as [E0|(Hpj & Hhome & Hrav & _)]; [contradiction|].
destruct (s8c_pj_n SEGS _ _ _ _ _ Hpj ltac:(destruct o; [right|left]; exact Htag)) as (Hn40 & Hnv).
destruct Hcur as (P0 & P8 & P16 & P24 & P32).
pose proof HPRE as HPRE'. unfold ev_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdl01 & _ & _ & _ & _ & Hvt & _).
destruct Hvt as [E0|(_ & _ & Hfoot)]; [contradiction|].
assert (HF1 : forall z, ea_v a <= z < ea_v a + 56 ->
    ~ (ea_q a <= z < ea_q a + 40) /\ ~ (spZ (ea_regs a) - ea_STK a <= z < spZ (ea_regs a)))
  by (intros z Hz; destruct (Hfoot z (or_introl Hz)) as (_ & H1 & H2 & _); split; assumption).
assert (Hvq : ea_v a + 56 <= ea_q a \/ ea_q a + 40 <= ea_v a).
{ destruct (Z_lt_le_dec (ea_v a) (ea_q a)) as [h|h]; [left|right].
  - destruct (Z_lt_le_dec (ea_q a) (ea_v a + 56)) as [h2|h2]; [|lia].
    exfalso. destruct (HF1 (ea_q a) ltac:(lia)) as (Hn & _). lia.
  - destruct (Z_lt_le_dec (ea_v a) (ea_q a + 40)) as [h2|h2]; [|lia].
    exfalso. destruct (HF1 (ea_v a) ltac:(lia)) as (Hn & _). lia. }
assert (HvS : ea_v a + 56 <= ea_sp0 a - ea_STK a \/ ea_sp0 a <= ea_v a).
{ destruct (Z_lt_le_dec (ea_v a) (ea_sp0 a)) as [h|h]; [left|right; exact h].
  destruct (Z_lt_le_dec (ea_sp0 a - ea_STK a) (ea_v a + 56)) as [h2|h2]; [|lia].
  exfalso. destruct (Z_lt_le_dec (ea_v a) (ea_sp0 a - ea_STK a)) as [h3|h3].
  - assert (Hz : ea_v a <= ea_sp0 a - ea_STK a < ea_v a + 56) by lia.
    destruct (HF1 _ Hz) as (_ & Hn). unfold ea_sp0 in *. lia.
  - assert (Hz : ea_v a <= ea_v a < ea_v a + 56) by lia.
    destruct (HF1 _ Hz) as (_ & Hn). unfold ea_sp0 in *. lia. }
assert (HS1 : ea_sp0 a - 288 <= ea_S1 a <= ea_sp0 a - 256).
{ unfold ea_S1, ea_SA. pose proof (Z.mod_pos_bound (ea_sp0 a - 256) 32 ltac:(lia)). lia. }
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (s8c_E10_x regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) as (X32 & X33 & X34).
set (E := s8c_E10 regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) in *.
assert (E9 : ew E 9 = w64 (ea_S1 a)) by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 9 9%bv) by (lia || reflexivity); exact R9).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E23 : ew E 23 = w64 (ea_v a))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 23 23%bv) by (lia || reflexivity); exact H23).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (E11 : ew E 11 = w64 (Z.of_nat (length acc)))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 11 11%bv) by (lia || reflexivity); exact H11).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = ea_v a) by (rewrite E23; unfold w64; apply unsigned_lit_small; lia).
assert (Hpres : forall o0, 0 <= o0 < 40 -> writable_at SEGS (mrestrict (w_H W) mem) (ea_q a + o0)).
{ intros o0 Ho0. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). apply Hpr. unfold ea_sp0 in *. lia. }
rewrite restrict_mkst_fx. unfold ss10v. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_sp10 r_qdep r_qdl r_vn].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (ea_q a + 16)); [lia | | exact Hs48].
      apply bv_eq. change (bv_unsigned (sv_denot E (SOff 19 16))) with (U E (SOff 19 16)).
      rewrite (U_atom_off E 19 (ea_q a) 16 E19) by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (shadow_addr (ea_q a + 16))); [lia | | exact Hs56].
      apply (s8c_U_shx E 19 16 (ea_q a) E19); [lia | lia | exact E24].
  + rewrite U19. split; [lia|]. split; [lia|]. split.
    * intros o0 Ho0. apply Hpres. lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (s8c_chunk_of_val SEGS E _ _ _ 4 _ (ea_dep a + 1)); [lia | | exact P16].
      cbn [sv_denot]. rewrite X33. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  + rewrite U19. split; [lia|]. split; [lia|]. split.
    * intros o0 Ho0. apply Hpres. lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (s8c_chunk_of_val SEGS E _ _ _ 4 _ dln); [lia | | exact P32].
      cbn [sv_denot]. rewrite X34. unfold w64. rewrite unsigned_lit_small by (destruct Hdl0 as (H01 & _); lia).
      rewrite Z.add_0_r. reflexivity.
  + rewrite U23. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (Z.of_nat (length (ev_kids (ea_t a))))); [lia | | exact Hn40].
    cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val r_sp10 r_qdep r_qdl r_vn]. rewrite U9, U19, U23.
  unfold ea_sp0 in *. repeat split; lia.
- split; [|split; [|exact I]].
  + cbn [f_atoms atoms_ok fa_bx fa_q fa_v fa_dep]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    unfold PjGrammar.MAXD. cbn [Z.of_nat Pos.of_succ_nat].
    rewrite U19, U23, E24, X33. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
    repeat split; try lia.
  + cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot].
    rewrite E11, X32, !Z.add_0_r. unfold w64. rewrite !Z_to_bv_bv_unsigned. exact Hc.
Qed.

(* the cut state of piece 10 with v' = 0 (no node to compare: s7 pinned to 0) *)
Lemma s8c_st10z : forall a W regs mem md ly S Hp k o acc i dln fxc,
  EVPRE a -> EVEND a W regs mem md ly S Hp k o acc i dln -> ev_v' (ea_v a) o (ea_t a) = 0 ->
  @st_ok_pi SEGS VAL fxc (s8c_E10 regs 0 (ea_dep a + 1) dln) ss10z
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (VAL A_TEXT + ev_k EV_END)) mem (seg_rom SEGS))).
Proof.
intros a W regs mem md ly S Hp k o acc i dln fxc HPRE HEND Hv'.
destruct HEND as (HMID & Hregs & H22 & H23 & H11 & Hs48 & Hs56 & Hdep31 & Hi & HV & Hdl0).
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite Hv' in H23.
pose proof HMID as (HJ & _ & _ & _ & HL & Hcur & _ & _ & _ & _).
destruct Hcur as (P0 & P8 & P16 & P24 & P32).
assert (HS1 : ea_sp0 a - 288 <= ea_S1 a <= ea_sp0 a - 256).
{ unfold ea_S1, ea_SA. pose proof (Z.mod_pos_bound (ea_sp0 a - 256) 32 ltac:(lia)). lia. }
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (s8c_E10_x regs 0 (ea_dep a + 1) dln) as (X32 & X33 & X34).
set (E := s8c_E10 regs 0 (ea_dep a + 1) dln) in *.
assert (E9 : ew E 9 = w64 (ea_S1 a)) by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 9 9%bv) by (lia || reflexivity); exact R9).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (Hpres : forall o0, 0 <= o0 < 40 -> writable_at SEGS (mrestrict (w_H W) mem) (ea_q a + o0)).
{ intros o0 Ho0. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). apply Hpr. unfold ea_sp0 in *. lia. }
rewrite restrict_mkst_fx. unfold ss10z. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact H23].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_sp10 r_qdep r_qdl].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (ea_q a + 16)); [lia | | exact Hs48].
      apply bv_eq. change (bv_unsigned (sv_denot E (SOff 19 16))) with (U E (SOff 19 16)).
      rewrite (U_atom_off E 19 (ea_q a) 16 E19) by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (shadow_addr (ea_q a + 16))); [lia | | exact Hs56].
      apply (s8c_U_shx E 19 16 (ea_q a) E19); [lia | lia | exact E24].
  + rewrite U19. split; [lia|]. split; [lia|]. split.
    * intros o0 Ho0. apply Hpres. lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (s8c_chunk_of_val SEGS E _ _ _ 4 _ (ea_dep a + 1)); [lia | | exact P16].
      cbn [sv_denot]. rewrite X33. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  + rewrite U19. split; [lia|]. split; [lia|]. split.
    * intros o0 Ho0. apply Hpres. lia.
    * apply Forall_cons; [|apply Forall_nil].
      apply (s8c_chunk_of_val SEGS E _ _ _ 4 _ dln); [lia | | exact P32].
      cbn [sv_denot]. rewrite X34. unfold w64. rewrite unsigned_lit_small by (destruct Hdl0 as (H01 & _); lia).
      rewrite Z.add_0_r. reflexivity.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val r_sp10 r_qdep r_qdl]. rewrite U9, U19.
  unfold ea_sp0 in *. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms atoms_ok fa_bx fa_q fa_dep]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  unfold PjGrammar.MAXD. cbn [Z.of_nat Pos.of_succ_nat].
  rewrite U19, E24, X33. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
  repeat split; try lia.
Qed.

(* a region of a symbolic state is region_ok at its machine state *)
Lemma s8c_reg_ok : forall fxc E ss ms r, @st_ok_pi SEGS VAL fxc E ss ms -> In r (ss_mem ss) ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
intros fxc E ss ms r HS Hin. unfold st_ok_pi, st_ok in HS.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hro & _) & _). rewrite Forall_forall in Hro. exact (Hro r Hin).
Qed.

(* piece 10, v' <> 0 and n = v'->n: differs kept *)
Lemma s8c_end_veq : s8c_ZB -> forall a fxc W regs mem md ly S Hp k o acc i dln,
  EVPRE a -> @ev_fx fx fxc -> EVEND a W regs mem md ly S Hp k o acc i dln ->
  ev_v' (ea_v a) o (ea_t a) <> 0 ->
  branch_taken BC_EQ (w64 (Z.of_nat (length acc))) (w64 (Z.of_nat (length (ev_kids (ea_t a))))) = true ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc regs EV_END mem md) (EVEXIT a).
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND Hv' Hm.
pose proof (s8c_st10v BC_EQ a W regs mem md ly S Hp k o acc i dln fxc HPRE HEND Hv' Hm) as HS.
set (E := s8c_E10 regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (ev_kids (ea_t a)))); w64 (ea_dep a + 1); w64 dln]) E)
  by (split; [intros n Hn; unfold E, s8c_E10; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS EV_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof HEND as ((HJ & _) & _).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (ev_pc EV_END) with (VAL A_TEXT + ev_k EV_END) by (vm_compute; reflexivity).
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HEND as (HMID & Hregs & H22 & H23 & H11 & Hs48 & Hs56 & Hdep31 & Hi & HV & Hdl0).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (s8c_v'_nz _ _ _ Hv') as [Hv0 Htag].
pose proof (s8c_v_bound _ _ _ _ _ _ _ _ _ _ _ HPRE HMID Hv0) as Hvb.
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (E23 : ew E 23 = w64 (ea_v a)).
{ unfold E; rewrite (s8c_E10_reg _ _ _ _ 23 23%bv) by (lia || reflexivity). rewrite H23.
  unfold ev_v', ev_tv. rewrite Htag, Z.eqb_refl, orb_true_r. reflexivity. }
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EV_Bx = SHADOW_OFF) by (unfold EV_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN EV_Bspan (ev_k EV_EXIT).
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom_off E 19 (ea_q a) 16 E19) by lia.
  apply (range_addressable_sub _ _ (ea_q a) 40); [exact (s8c_q_ra ZB a ly S Hp W mem md k _ _ _ HPRE HMID) | lia | lia].
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom_off E 23 (ea_v a) 40 E23) by lia.
  pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
  destruct Htree as [E0|(_ & _ & Hrav & _)]; [contradiction|].
  apply (range_addressable_sub _ _ (ea_v a) 56); [exact Hrav | lia | lia].
- intros z (r & Hin & Hz). unfold ss10v in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp10 r_qdep r_qdl r_vn] in Hz;
    try lia; left; rewrite U19 in Hz; unfold ea_sp0 in *; lia.
- pmkst HS. apply SRr_ret.
  match goal with |- EVEXIT a W {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom; cfg_model := ?d |} =>
    replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT) by (vm_compute; reflexivity);
    change {| cfg_ms := YK11.mkst r (Z_to_bv 64 (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT)) m rom;
              cfg_model := d |} with (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc r EV_EXIT m d) end.
  destruct (s8c_E10_x regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) as (X32 & X33 & X34).
  fold E in X32, X33, X34.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_introl eq_refl))) as Rd.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_intror (or_introl eq_refl)))) as Rl.
  unfold region_ok in Rd, Rl. cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Rd, Rl.
  destruct Rd as (_ & _ & _ & Rd). destruct Rl as (_ & _ & _ & Rl). apply Forall_inv in Rd, Rl.
  apply (s8c_val_of_chunk SEGS) in Rd; [|lia]. apply (s8c_val_of_chunk SEGS) in Rl; [|lia].
  cbn [sv_denot] in Rd, Rl. rewrite !ew_ewset_other in Rd, Rl by lia. rewrite U19 in Rd, Rl.
  rewrite X33 in Rd. rewrite X34 in Rl. unfold w64 in Rd, Rl.
  assert (Hdl01 : 0 <= dln < 2 ^ 64) by (destruct Hdl0 as (H01 & _); lia).
  rewrite (unsigned_lit_small (ea_dep a + 1)) in Rd by lia.
  replace (ea_dep a + 1 + -1) with (ea_dep a) in Rd by lia. rewrite (unsigned_lit_small (ea_dep a)) in Rd by lia.
  rewrite (unsigned_lit_small dln) in Rl by exact Hdl01. rewrite Z.add_0_r in Rl.
  rewrite (unsigned_lit_small dln) in Rl by exact Hdl01.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ s8c_kept HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (27%bv : bv 5) Q27.
  apply (s8c_end_post a fxc W regs mem md ly S Hp k o acc i dln _ _ _ dln HPRE HFX HEND HJ HMN).
  + intros x Hx. apply HF. intros (r & Hin & Hz). apply Hx. unfold ss10v in Hin. cbn [ss_mem] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp10 r_qdep r_qdl r_vn] in Hz;
      rewrite ?U19 in Hz; lia.
  + exact Rd.
  + exact Rl.
  + apply (s8c_dl_keep _ _ _ _ _ _ Hdl0). right.
    pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
    destruct Htree as [E0|(Hpj & _ & _)]; [contradiction|].
    destruct (s8c_pj_n SEGS _ _ _ _ _ Hpj ltac:(destruct o; [right|left]; exact Htag)) as (_ & Hnv).
    cbn [branch_taken] in Hm. unfold bv_eqb, w64 in Hm. apply Z.eqb_eq in Hm. rewrite !Z_to_bv_unsigned in Hm.
    unfold bv_wrap in Hm. change (bv_modulus 64) with (2 ^ 64) in Hm.
    rewrite (Z.mod_small (Z.of_nat (length (ev_kids (ea_t a))))) in Hm by lia.
    pose proof (Z.mod_le (Z.of_nat (length acc)) (2 ^ 64) ltac:(lia) ltac:(lia)). lia.
  + exact HK.
  + exact Q27.
Qed.

(* piece 10, v' <> 0 and n <> v'->n (the machine's 64-bit compare): differs := 1 (C :290), its ASan check at 0x83d1c *)
Lemma s8c_end_vne : s8c_ZB -> forall a fxc W regs mem md ly S Hp k o acc i dln,
  EVPRE a -> @ev_fx fx fxc -> EVEND a W regs mem md ly S Hp k o acc i dln ->
  ev_v' (ea_v a) o (ea_t a) <> 0 ->
  branch_taken BC_NE (w64 (Z.of_nat (length acc))) (w64 (Z.of_nat (length (ev_kids (ea_t a))))) = true ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc regs EV_END mem md) (EVEXIT a).
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND Hv' Hm.
pose proof (s8c_st10v BC_NE a W regs mem md ly S Hp k o acc i dln fxc HPRE HEND Hv' Hm) as HS.
set (E := s8c_E10 regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (ev_kids (ea_t a)))); w64 (ea_dep a + 1); w64 dln]) E)
  by (split; [intros n Hn; unfold E, s8c_E10; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS EV_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof HEND as ((HJ & _) & _).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (ev_pc EV_END) with (VAL A_TEXT + ev_k EV_END) by (vm_compute; reflexivity).
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HEND as (HMID & Hregs & H22 & H23 & H11 & Hs48 & Hs56 & Hdep31 & Hi & HV & Hdl0).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (s8c_v'_nz _ _ _ Hv') as [Hv0 Htag].
pose proof (s8c_v_bound _ _ _ _ _ _ _ _ _ _ _ HPRE HMID Hv0) as Hvb.
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (E23 : ew E 23 = w64 (ea_v a)).
{ unfold E; rewrite (s8c_E10_reg _ _ _ _ 23 23%bv) by (lia || reflexivity). rewrite H23.
  unfold ev_v', ev_tv. rewrite Htag, Z.eqb_refl, orb_true_r. reflexivity. }
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EV_Bx = SHADOW_OFF) by (unfold EV_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
pose proof (s8c_q_ra ZB a ly S Hp W mem md k _ _ _ HPRE HMID) as HQRA.
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN EV_Bspan (ev_k EV_EXIT).
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom_off E 19 (ea_q a) 16 E19) by lia.
  apply (range_addressable_sub _ _ (ea_q a) 40); [exact HQRA | lia | lia].
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom_off E 19 (ea_q a) 32 E19) by lia.
  apply (range_addressable_sub _ _ (ea_q a) 40); [exact HQRA | lia | lia].
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom_off E 23 (ea_v a) 40 E23) by lia.
  pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
  destruct Htree as [E0|(_ & _ & Hrav & _)]; [contradiction|].
  apply (range_addressable_sub _ _ (ea_v a) 56); [exact Hrav | lia | lia].
- intros z (r & Hin & Hz). unfold ss10v in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp10 r_qdep r_qdl r_vn] in Hz;
    try lia; left; rewrite U19 in Hz; unfold ea_sp0 in *; lia.
- pmkst HS. apply SRr_ret.
  match goal with |- EVEXIT a W {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom; cfg_model := ?d |} =>
    replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT) by (vm_compute; reflexivity);
    change {| cfg_ms := YK11.mkst r (Z_to_bv 64 (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT)) m rom;
              cfg_model := d |} with (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc r EV_EXIT m d) end.
  destruct (s8c_E10_x regs (Z.of_nat (length (ev_kids (ea_t a)))) (ea_dep a + 1) dln) as (X32 & X33 & X34).
  fold E in X32, X33, X34.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_introl eq_refl))) as Rd.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_intror (or_introl eq_refl)))) as Rl.
  unfold region_ok in Rd, Rl. cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Rd, Rl.
  destruct Rd as (_ & _ & _ & Rd). destruct Rl as (_ & _ & _ & Rl). apply Forall_inv in Rd, Rl.
  apply (s8c_val_of_chunk SEGS) in Rd; [|lia]. apply (s8c_val_of_chunk SEGS) in Rl; [|lia].
  cbn [sv_denot ew ewset Nat.eqb] in Rd, Rl. rewrite U19 in Rd, Rl.
  rewrite X33 in Rd. unfold w64 in Rd.
  rewrite (unsigned_lit_small (ea_dep a + 1)) in Rd by lia.
  replace (ea_dep a + 1 + -1) with (ea_dep a) in Rd by lia. rewrite (unsigned_lit_small (ea_dep a)) in Rd by lia.
  rewrite (unsigned_lit_small 1) in Rl by lia.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ s8c_kept HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (27%bv : bv 5) Q27.
  apply (s8c_end_post a fxc W regs mem md ly S Hp k o acc i dln _ _ _ 1 HPRE HFX HEND HJ HMN).
  + intros x Hx. apply HF. intros (r & Hin & Hz). apply Hx. unfold ss10v in Hin. cbn [ss_mem] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp10 r_qdep r_qdl r_vn] in Hz;
      rewrite ?U19 in Hz; lia.
  + exact Rd.
  + exact Rl.
  + apply (s8c_dl_set _ _ _ _ _ Hv'). intros Heq.
    cbn [branch_taken] in Hm. unfold bv_eqb, w64 in Hm. rewrite Heq, Z.eqb_refl in Hm. discriminate Hm.
  + exact HK.
  + exact Q27.
Qed.

(* piece 10, v' = 0: the `beqz s7` at 0x83cf0 skips the count; differs kept *)
Lemma s8c_end_z : s8c_ZB -> forall a fxc W regs mem md ly S Hp k o acc i dln,
  EVPRE a -> @ev_fx fx fxc -> EVEND a W regs mem md ly S Hp k o acc i dln ->
  ev_v' (ea_v a) o (ea_t a) = 0 ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc regs EV_END mem md) (EVEXIT a).
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND Hv'.
pose proof (s8c_st10z a W regs mem md ly S Hp k o acc i dln fxc HPRE HEND Hv') as HS.
set (E := s8c_E10 regs 0 (ea_dep a + 1) dln) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 0; w64 (ea_dep a + 1); w64 dln]) E)
  by (split; [intros n Hn; unfold E, s8c_E10; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS EV_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof HEND as ((HJ & _) & _).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (ev_pc EV_END) with (VAL A_TEXT + ev_k EV_END) by (vm_compute; reflexivity).
pose proof (s8c_pre_q a HPRE) as (Hsp & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HEND as (HMID & Hregs & H22 & H23 & H11 & Hs48 & Hs56 & Hdep31 & Hi & HV & Hdl0).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (s8c_E10_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EV_Bx = SHADOW_OFF) by (unfold EV_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
pose proof (s8c_q_ra ZB a ly S Hp W mem md k _ _ _ HPRE HMID) as HQRA.
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN EV_Bspan (ev_k EV_EXIT).
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom_off E 19 (ea_q a) 16 E19) by lia.
  apply (range_addressable_sub _ _ (ea_q a) 40); [exact HQRA | lia | lia].
- intros z (r & Hin & Hz). unfold ss10z in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp10 r_qdep r_qdl] in Hz;
    try lia; left; rewrite U19 in Hz; unfold ea_sp0 in *; lia.
- pmkst HS. apply SRr_ret.
  match goal with |- EVEXIT a W {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom; cfg_model := ?d |} =>
    replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT) by (vm_compute; reflexivity);
    change {| cfg_ms := YK11.mkst r (Z_to_bv 64 (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT)) m rom;
              cfg_model := d |} with (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc r EV_EXIT m d) end.
  destruct (s8c_E10_x regs 0 (ea_dep a + 1) dln) as (X32 & X33 & X34).
  fold E in X32, X33, X34.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_introl eq_refl))) as Rd.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_intror (or_introl eq_refl)))) as Rl.
  unfold region_ok in Rd, Rl. cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Rd, Rl.
  destruct Rd as (_ & _ & _ & Rd). destruct Rl as (_ & _ & _ & Rl). apply Forall_inv in Rd, Rl.
  apply (s8c_val_of_chunk SEGS) in Rd; [|lia]. apply (s8c_val_of_chunk SEGS) in Rl; [|lia].
  cbn [sv_denot ew ewset Nat.eqb] in Rd, Rl. rewrite U19 in Rd, Rl.
  rewrite X33 in Rd. rewrite X34 in Rl. unfold w64 in Rd, Rl.
  assert (Hdl01 : 0 <= dln < 2 ^ 64) by (destruct Hdl0 as (H01 & _); lia).
  rewrite (unsigned_lit_small (ea_dep a + 1)) in Rd by lia.
  replace (ea_dep a + 1 + -1) with (ea_dep a) in Rd by lia. rewrite (unsigned_lit_small (ea_dep a)) in Rd by lia.
  rewrite (unsigned_lit_small dln) in Rl by exact Hdl01. rewrite Z.add_0_r in Rl.
  rewrite (unsigned_lit_small dln) in Rl by exact Hdl01.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ s8c_kept HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (27%bv : bv 5) Q27.
  apply (s8c_end_post a fxc W regs mem md ly S Hp k o acc i dln _ _ _ dln HPRE HFX HEND HJ HMN).
  + intros x Hx. apply HF. intros (r & Hin & Hz). apply Hx. unfold ss10z in Hin. cbn [ss_mem] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp10 r_qdep r_qdl] in Hz;
      rewrite ?U19 in Hz; lia.
  + exact Rd.
  + exact Rl.
  + exact (s8c_dl_keep _ _ _ _ _ _ Hdl0 (or_introl Hv')).
  + exact HK.
  + exact Q27.
Qed.

(* ======== PIECE 10 (0x83cec-0x83d44 with the report arms 0x83e6c-0x83e7c, 0x83ed8-0x83ee4, 0x84008; 33
   instructions): P_END -> P_EXIT. Under ZB only (the per-byte stack zero-shadow law, alx_zshadow_byte). ======== *)
Lemma ev_items_end_holds_zb : s8c_ZB ->
  ev_items_end_spec (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND.
destruct (Z.eq_dec (ev_v' (ea_v a) o (ea_t a)) 0) as [Hz|Hnz].
- exact (s8c_end_z ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND Hz).
- destruct (branch_taken BC_EQ (w64 (Z.of_nat (length acc))) (w64 (Z.of_nat (length (ev_kids (ea_t a)))))) eqn:Hm.
  + exact (s8c_end_veq ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND Hnz Hm).
  + apply (s8c_end_vne ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HEND Hnz).
    cbn [branch_taken] in Hm |- *. rewrite Hm. reflexivity.
Qed.

(* ======== piece 9: P_CLOSE -> P_END (the closer consumed) or P_EXIT (refusal) ======== *)
#[local] Notation EVCLOSE := (@ev_at_close rc CfParams_preset prh_img_A RL A_prog_listing PI_prog_A B ARx SK).
(* the environment of piece 9: the registers, then the byte at x0 + i, the closer, s1 + 120 *)
Definition s8c_E9 (regs : bvmap 5 word) (c cl n1 : Z) : env := Eimg (Ereg regs [w64 c; w64 cl; w64 n1]).
Lemma s8c_E9_reg : forall regs c cl n1 (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (s8c_E9 regs c cl n1) n = getr regs r.
Proof. intros regs c cl n1 n r Hn Hr. unfold s8c_E9. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma s8c_E9_x : forall regs c cl n1,
  ew (s8c_E9 regs c cl n1) 32 = w64 c /\ ew (s8c_E9 regs c cl n1) 33 = w64 cl /\ ew (s8c_E9 regs c cl n1) 34 = w64 n1.
Proof.
intros. unfold s8c_E9. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 0)|]. split; [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)].
Qed.
Definition s8c_E9a (a : ev_act) (regs : bvmap 5 word) (o : bool) (acc : list (list Z * PjTree.jv)) (i : nat) : env :=
  s8c_E9 regs (nth i (ea_x a) 0) (PjGrammar.closer o) (Z.of_nat (length acc) - 1).

(* the cut state of piece 9, the comparison byte = closer assumed as the condition c *)
Lemma s8c_st9 : forall c a W regs mem md ly S Hp k o acc i dln fxc,
  EVPRE a -> EVCLOSE a W regs mem md ly S Hp k o acc i dln ->
  branch_taken c (w64 (nth i (ea_x a) 0)) (w64 (PjGrammar.closer o)) = true ->
  @st_ok_pi SEGS VAL fxc (s8c_E9a a regs o acc i) (ss9 c)
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (VAL A_TEXT + ev_k EV_CLOSE)) mem (seg_rom SEGS))).
Proof.
intros c a W regs mem md ly S Hp k o acc i dln fxc HPRE HCL Hc.
destruct HCL as (HMID & Hregs & H20 & H21 & H22 & H23 & H27 & H10 & H11 & Hsp & H104 & H120 & Hdep31 & Hi & Hacc &
  Hn44 & Hws & HV & Hdl0).
pose proof (s8c_pre_q a HPRE) as (Hsp0 & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HMID as (HJ & _ & _ & _ & HL & Hcur & Hsrc & _).
destruct Hcur as (P0 & P8 & P16 & P24 & P32).
destruct Hsrc as (Hbytes & Hx4 & Hxc & _).
destruct (Hbytes i Hi) as [Hb1 Hb256].
destruct Hsp as (S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
assert (HS1 : ea_sp0 a - 288 <= ea_S1 a <= ea_sp0 a - 256).
{ unfold ea_S1, ea_SA. pose proof (Z.mod_pos_bound (ea_sp0 a - 256) 32 ltac:(lia)). lia. }
assert (Hlx : Z.of_nat i < ea_len a) by (unfold ea_len; lia).
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
unfold s8c_E9a.
destruct (s8c_E9_x regs (nth i (ea_x a) 0) (PjGrammar.closer o) (Z.of_nat (length acc) - 1)) as (X32 & X33 & X34).
set (E := s8c_E9 regs (nth i (ea_x a) 0) (PjGrammar.closer o) (Z.of_nat (length acc) - 1)) in *.
assert (E9 : ew E 9 = w64 (ea_S1 a)) by (unfold E; rewrite (s8c_E9_reg _ _ _ _ 9 9%bv) by (lia || reflexivity); exact R9).
assert (E10 : ew E 10 = w64 (ea_x0 a + Z.of_nat i))
  by (unfold E; rewrite (s8c_E9_reg _ _ _ _ 10 10%bv) by (lia || reflexivity); exact H10).
assert (E18 : ew E 18 = w64 (ea_fr a))
  by (unfold E; rewrite (s8c_E9_reg _ _ _ _ 18 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E; rewrite (s8c_E9_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E; rewrite (s8c_E9_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (U9 : bv_unsigned (ew E 9) = ea_S1 a) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = ea_x0 a + Z.of_nat i) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (Hpres : forall o0, 0 <= o0 < 40 -> writable_at SEGS (mrestrict (w_H W) mem) (ea_q a + o0)).
{ intros o0 Ho0. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). apply Hpr. unfold ea_sp0 in *. lia. }
assert (Hcl : PjGrammar.closer o = 93 \/ PjGrammar.closer o = 125) by (destruct o; cbn; auto).
rewrite restrict_mkst_fx. unfold ss9. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
  + rewrite H11, (s8c_U_shx E 10 0 (ea_x0 a + Z.of_nat i) E10); [rewrite Z.add_0_r; reflexivity | lia | lia | exact E24].
  + rewrite R26, (s8c_U_shx E 19 0 (ea_q a) E19); [rewrite Z.add_0_r; reflexivity | lia | lia | exact E24].
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val r_sp9 r_txt r_qp].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (ea_fr a)); [lia | | exact S24].
      cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (PjGrammar.closer o)); [lia | | exact S64].
      cbn [sv_denot]. rewrite X33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (Z.of_nat (length acc) - 1)); [lia | | exact H120].
      cbn [sv_denot]. rewrite X34, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite U10. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (s8c_chunk_of_val SEGS E _ _ _ 1 _ (nth i (ea_x a) 0)); [lia | | rewrite Z.add_0_r; exact Hb1].
    cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o0 Ho0; apply Hpres; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (s8c_chunk_of_val SEGS E _ _ _ 8 _ (ea_x0 a + Z.of_nat i)); [lia | | rewrite Z.add_0_r; exact P0].
    cbn [sv_denot]. rewrite E10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val r_sp9 r_txt r_qp]. rewrite U9, U10, U19.
  unfold ea_sp0 in *. repeat split; lia.
- split; [|split; [|exact I]].
  + cbn [f_atoms atoms_ok fa_bx fa_q fa_p fa_c]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U19, E24, X32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
    repeat split; try lia.
  + cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot].
    rewrite X32, X33, !Z.add_0_r. unfold w64. rewrite !Z_to_bv_bv_unsigned. exact Hc.
Qed.

(* the registers piece 9 leaves (s6 is reloaded from s1 + 24, s10 stays the shadow of q) *)
Definition s8c_kept9 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 23; 24; 25]%bv.
(* after piece 9: EV_MID with in->p at x0 + p', the registers of ev_regs, the spills piece 10 reads *)
Lemma s8c_close_mid : forall a W regs mem md ly S Hp k o acc i dln regs' mem' md' p',
  EVPRE a -> EVCLOSE a W regs mem md ly S Hp k o acc i dln ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  YAkMemnorm.memnorm SEGS mem' ->
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) -> mem' x = mem x) ->
  val_mem SEGS (rdW W mem') (ea_q a) 8 (ea_x0 a + p') ->
  (forall r, In r s8c_kept9 -> getr regs' r = getr regs r) -> getr regs' 26 = getr regs 26 ->
  EVMID a ly S Hp W mem' md' k (ea_x0 a + p') (ea_dep a + 1) dln /\ ev_regs a regs' /\
  val_mem SEGS (rdW W mem') (ea_S1 a + 48) 8 (ea_q a + 16) /\
  val_mem SEGS (rdW W mem') (ea_S1 a + 56) 8 (shadow_addr (ea_q a + 16)).
Proof.
intros a W regs mem md ly S Hp k o acc i dln regs' mem' md' p' HPRE HCL HJ' HMN' HF Hp0 Hkept H26.
destruct HCL as (HMID & Hregs & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
pose proof (s8c_pre_q a HPRE) as (Hsp0 & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS1 : ea_sp0 a - 288 <= ea_S1 a <= ea_sp0 a - 256).
{ unfold ea_S1, ea_SA. pose proof (Z.mod_pos_bound (ea_sp0 a - 256) 32 ltac:(lia)). lia. }
pose proof HMID as (_ & _ & _ & _ & _ & Hcur & _).
destruct Hcur as (P0 & P8 & P16 & P24 & P32).
destruct Hsp as (_ & _ & _ & S48 & S56 & _).
pose (C := fun z => ea_q a <= z < ea_q a + 8).
split; [|split; [|split]].
- apply (s8c_mid_frame a ly S Hp W mem md k _ _ _ mem' md' _ _ _ HPRE HMID HJ').
  + split; [lia|]. intros x Hx. apply HF. intros Hc. apply Hx. unfold qw. lia.
  + split; [exact Hp0|]. split; [|split; [|split]].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P8].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P16].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P24].
    * apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact P32].
  + exact HMN'.
- unfold ev_regs in *. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
  repeat split; first [rewrite H26; assumption | rewrite Hkept by (cbv; tauto); assumption].
- apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact S48].
- apply (s8c_val_C SEGS C mem mem' _ _ _ _ HF); [lia | simpl Z.of_nat; lia | intros; unfold C; lia | exact S56].
Qed.

(* the shared tail of both arms of piece 9: the final registers of interest *)
Ltac s8c_regs9 HS q E19 E24 E18 Q22 Q26 Q27 :=
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 22%bv HS) as Q22;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 26%bv HS) as Q26;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as Q27;
  change (sr_get _ 22%bv) with (SOff 18 0) in Q22; change (sr_get _ 26%bv) with (shx 19 0) in Q26;
  change (sr_get _ 27%bv) with (SLit 18446744073709551615) in Q27;
  cbn [ms_regs restrict] in Q22, Q26, Q27;
  cbn [sv_denot ew ewset Nat.eqb] in Q22; rewrite E18, Z.add_0_r in Q22; unfold w64 in Q22;
  rewrite Z_to_bv_bv_unsigned in Q22;
  lazymatch type of Q26 with context [sv_denot ?E' (shx 19 0)] =>
    rewrite (s8c_U_shx E' 19 0 q) in Q26;
      [| cbn [ew ewset Nat.eqb]; exact E19 | lia | lia | cbn [ew ewset Nat.eqb]; exact E24] end;
  rewrite Z.add_0_r in Q26.

(* piece 9, the byte is not the closer: the refusal (s11 = -1 at 0x83cc8), to P_EXIT, nothing written *)
Lemma s8c_close_refuse : s8c_ZB -> forall a fxc W regs mem md ly S Hp k o acc i dln,
  EVPRE a -> @ev_fx fx fxc -> EVCLOSE a W regs mem md ly S Hp k o acc i dln ->
  nth i (ea_x a) 0 <> PjGrammar.closer o ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc regs EV_CLOSE mem md) (EVEXIT a).
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HCL Hne.
assert (Hcl : PjGrammar.closer o = 93 \/ PjGrammar.closer o = 125) by (destruct o; cbn; auto).
pose proof HCL as (HMID & Hregs & H20 & H21 & H22 & H23 & H27 & H10 & H11 & Hsp & H104 & H120 & Hdep31 & Hi & Hacc &
  Hn44 & Hws & HV & Hdl0).
pose proof HMID as (_ & _ & _ & _ & _ & _ & Hsrc & _). destruct Hsrc as (Hbytes & Hx4 & Hxc & _ & Hrax & _).
destruct (Hbytes i Hi) as [_ Hb256].
pose proof (s8c_st9 BC_NE a W regs mem md ly S Hp k o acc i dln fxc HPRE HCL) as HS.
specialize (HS ltac:(cbn [branch_taken]; unfold bv_eqb, w64; rewrite !unsigned_lit_small by lia;
  apply Bool.negb_true_iff, Z.eqb_neq; exact Hne)).
set (E := s8c_E9a a regs o acc i) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (nth i (ea_x a) 0); w64 (PjGrammar.closer o); w64 (Z.of_nat (length acc) - 1)]) E)
  by (split; [intros n Hn; unfold E, s8c_E9a, s8c_E9; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS EV_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof HMID as (HJ & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (ev_pc EV_CLOSE) with (VAL A_TEXT + ev_k EV_CLOSE) by (vm_compute; reflexivity).
pose proof (s8c_pre_q a HPRE) as (Hsp0 & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
assert (Hlx : Z.of_nat i < ea_len a) by (unfold ea_len; lia).
assert (E10 : ew E 10 = w64 (ea_x0 a + Z.of_nat i))
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 10 10%bv) by (lia || reflexivity); exact H10).
assert (E18 : ew E 18 = w64 (ea_fr a))
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 18 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EV_Bx = SHADOW_OFF) by (unfold EV_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN EV_Bspan (ev_k EV_EXIT).
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom E 10 (ea_x0 a + Z.of_nat i) E10) by lia.
  apply (range_addressable_sub _ _ (ea_x0 a) (ea_len a)); [exact Hrax | lia | lia].
- intros z (r & Hin & Hz). unfold ss9 in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp9 r_txt r_qp] in Hz;
    try lia; left; rewrite U19 in Hz; unfold ea_sp0 in *; lia.
- pmkst HS. apply SRr_ret.
  match goal with |- EVEXIT a W {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom; cfg_model := ?d |} =>
    replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT) by (vm_compute; reflexivity);
    change {| cfg_ms := YK11.mkst r (Z_to_bv 64 (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_EXIT)) m rom;
              cfg_model := d |} with (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc r EV_EXIT m d) end.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_intror (or_introl eq_refl)))) as Rp.
  unfold region_ok in Rp. cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Rp.
  destruct Rp as (_ & _ & _ & Rp). apply Forall_inv in Rp.
  apply (s8c_val_of_chunk SEGS) in Rp; [|lia].
  cbn [sv_denot ew ewset Nat.eqb] in Rp. rewrite U19, E10, Z.add_0_r, Z.add_0_r in Rp. unfold w64 in Rp.
  rewrite (unsigned_lit_small (ea_x0 a + Z.of_nat i)) in Rp by lia.
  rewrite (unsigned_lit_small (ea_x0 a + Z.of_nat i)) in Rp by lia.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ s8c_kept9 HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  s8c_regs9 HS (ea_q a) E19 E24 E18 Q22 Q26 Q27.
  destruct (s8c_close_mid a W regs mem md ly S Hp k o acc i dln (ms_regs ms) _ _ (Z.of_nat i) HPRE HCL HJ HMN)
    as (HMID' & HR' & _).
  + intros x Hx. apply HF. intros (r & Hin & Hz). apply Hx. unfold ss9 in Hin. cbn [ss_mem] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp9 r_txt r_qp] in Hz;
      rewrite ?U19 in Hz; lia.
  + exact Rp.
  + exact HK.
  + rewrite Q26, R26. reflexivity.
  + lazymatch goal with |- EVEXIT a W (ev_cfg _ ?r _ ?m ?d) =>
      exists fxc, r, m, d, ly, S, Hp, k, (-1), (Z.of_nat i), (ea_dep a + 1), dln end.
    split; [reflexivity|]. split; [exact HFX|]. split; [exact HMID'|]. split; [exact HR'|].
    split; [exact Q22|]. split.
    { rewrite Q27. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
    unfold ev_out. rewrite HV. replace (nth i (ea_x a) 0 =? PjGrammar.closer o) with false by (symmetry; apply Z.eqb_neq; exact Hne).
    split; [exact (proj1 Hdl0)|]. split; [reflexivity|]. split; [lia|]. lia.
Qed.

(* piece 9, the byte is the closer: in->p := x0 + i + 1, a1 := length acc, then piece 10 *)
Lemma s8c_close_cont : s8c_ZB -> forall a fxc W regs mem md ly S Hp k o acc i dln,
  EVPRE a -> @ev_fx fx fxc -> EVCLOSE a W regs mem md ly S Hp k o acc i dln ->
  nth i (ea_x a) 0 = PjGrammar.closer o ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc regs EV_CLOSE mem md) (EVEXIT a).
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HCL Heq.
pose proof HCL as (HMID & Hregs & H20 & H21 & H22 & H23 & H27 & H10 & H11 & Hsp & H104 & H120 & Hdep31 & Hi & Hacc &
  Hn44 & Hws & HV & Hdl0).
pose proof HMID as (_ & _ & _ & _ & _ & _ & Hsrc & _). destruct Hsrc as (Hbytes & Hx4 & Hxc & _ & Hrax & _).
pose proof (s8c_st9 BC_EQ a W regs mem md ly S Hp k o acc i dln fxc HPRE HCL) as HS.
specialize (HS ltac:(cbn [branch_taken]; rewrite Heq; unfold bv_eqb; apply Z.eqb_refl)).
set (E := s8c_E9a a regs o acc i) in HS.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (nth i (ea_x a) 0); w64 (PjGrammar.closer o); w64 (Z.of_nat (length acc) - 1)]) E)
  by (split; [intros n Hn; unfold E, s8c_E9a, s8c_E9; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS EV_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof HMID as (HJ & _).
pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose (RUNTOI := @paj_run_to_x_inv fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
unfold ev_cfg. replace (ev_pc EV_CLOSE) with (VAL A_TEXT + ev_k EV_CLOSE) by (vm_compute; reflexivity).
pose proof (s8c_pre_q a HPRE) as (Hsp0 & Hq0 & Hqd & Hdhi & H47 & Hlo & Hq8 & Hd0 & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold ev_regs in Hregs. destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
assert (Hlx : Z.of_nat i < ea_len a) by (unfold ea_len; lia).
destruct (s8c_E9_x regs (nth i (ea_x a) 0) (PjGrammar.closer o) (Z.of_nat (length acc) - 1)) as (X32 & X33 & X34).
change (s8c_E9 regs (nth i (ea_x a) 0) (PjGrammar.closer o) (Z.of_nat (length acc) - 1)) with E in X32, X33, X34.
assert (E10 : ew E 10 = w64 (ea_x0 a + Z.of_nat i))
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 10 10%bv) by (lia || reflexivity); exact H10).
assert (E18 : ew E 18 = w64 (ea_fr a))
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 18 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 19 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = w64 SHADOW_OFF)
  by (unfold E, s8c_E9a; rewrite (s8c_E9_reg _ _ _ _ 24 24%bv) by (lia || reflexivity); exact R24).
assert (U19 : bv_unsigned (ew E 19) = ea_q a) by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
assert (UBx : U E EV_Bx = SHADOW_OFF) by (unfold EV_Bx; apply (U_atom E 24 SHADOW_OFF E24); unfold SHADOW_OFF; lia).
pose proof (s8c_q_ra ZB a ly S Hp W mem md k _ _ _ HPRE HMID) as HQRA.
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN EV_Bspan (ev_k EV_END).
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom E 19 (ea_q a) E19) by lia.
  apply (range_addressable_sub _ _ (ea_q a) 40); [exact HQRA | lia | lia].
- cbn [ms_mem YK11.mkst]. rewrite <- aview_rd_of, UBx, (U_atom E 10 (ea_x0 a + Z.of_nat i) E10) by lia.
  apply (range_addressable_sub _ _ (ea_x0 a) (ea_len a)); [exact Hrax | lia | lia].
- intros z (r & Hin & Hz). unfold ss9 in Hin. cbn [ss_mem] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp9 r_txt r_qp] in Hz;
    try lia; left; rewrite U19 in Hz; unfold ea_sp0 in *; lia.
- pmkst HS.
  match goal with |- SRr _ W {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 ?pc) ?m ?rom; cfg_model := ?d |} _ =>
    replace pc with (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_END) by (vm_compute; reflexivity);
    change {| cfg_ms := YK11.mkst r (Z_to_bv 64 (ev_pc (L := A_prog_listing) (PA := PI_prog_A) EV_END)) m rom;
              cfg_model := d |} with (ev_cfg (L := A_prog_listing) (PA := PI_prog_A) fxc r EV_END m d) end.
  pose proof (s8c_reg_ok _ _ _ _ _ HS (or_intror (or_intror (or_introl eq_refl)))) as Rp.
  unfold region_ok in Rp. cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Rp.
  destruct Rp as (_ & _ & _ & Rp). apply Forall_inv in Rp.
  apply (s8c_val_of_chunk SEGS) in Rp; [|lia].
  cbn [sv_denot ew ewset Nat.eqb] in Rp. rewrite U19, E10, Z.add_0_r in Rp. unfold w64 in Rp.
  rewrite (unsigned_lit_small (ea_x0 a + Z.of_nat i)) in Rp by lia.
  rewrite (unsigned_lit_small (ea_x0 a + Z.of_nat i + 1)) in Rp by lia.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ s8c_kept9 HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  s8c_regs9 HS (ea_q a) E19 E24 E18 Q22 Q26 Q27.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11. change (sr_get _ 11%bv) with (SOff 34 1) in Q11.
  cbn [ms_regs restrict sv_denot ew ewset Nat.eqb] in Q11. rewrite X34 in Q11. unfold w64 in Q11.
  rewrite Z_to_bv_unsigned in Q11. unfold bv_wrap in Q11.
  assert (Q11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length acc))).
  { rewrite Q11. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia. }
  destruct (s8c_close_mid a W regs mem md ly S Hp k o acc i dln (ms_regs ms) _ _ (Z.of_nat (Nat.succ i)) HPRE HCL HJ HMN)
    as (HMID' & HR' & S48' & S56').
  + intros x Hx. apply HF. intros (r & Hin & Hz). apply Hx. unfold ss9 in Hin. cbn [ss_mem] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_sp9 r_txt r_qp] in Hz;
      rewrite ?U19 in Hz; lia.
  + rewrite Nat2Z.inj_succ. replace (ea_x0 a + Z.succ (Z.of_nat i)) with (ea_x0 a + Z.of_nat i + 1) by lia. exact Rp.
  + exact HK.
  + rewrite Q26, R26. reflexivity.
  + apply (ev_items_end_holds_zb ZB a fxc W _ _ _ ly S Hp k o acc (Nat.succ i) dln HPRE HFX).
    split; [exact HMID'|]. split; [exact HR'|]. split; [exact Q22|].
    split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|]. split; [exact Q11'|].
    split; [exact S48'|]. split; [exact S56'|]. split; [exact Hdep31|].
    split; [exact Hi|].
    split; [rewrite HV, Heq, Z.eqb_refl; reflexivity | exact Hdl0].
Qed.

(* ======== PIECES 9 + 10 (0x83cb8-0x83ce8 with the report arms 0x83ecc-0x83ed4, 0x84020-0x84024; then piece 10):
   P_CLOSE -> P_EXIT. Under ZB only. ======== *)
Lemma ev_items_close_holds_zb : s8c_ZB ->
  ev_items_close_spec (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof.
intros ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HCL.
destruct (Z.eq_dec (nth i (ea_x a) 0) (PjGrammar.closer o)) as [Heq|Hne].
- exact (s8c_close_cont ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HCL Heq).
- exact (s8c_close_refuse ZB a fxc W regs mem md ly S Hp k o acc i dln HPRE HFX HCL Hne).
Qed.

(* ======== PIECES 10 and 9 under LAWS only: s8c_ZB is AR_laws_x's field alx_zshadow_byte ======== *)
Lemma ev_items_end_holds :
  ev_items_end_spec (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof. exact (ev_items_end_holds_zb (alx_zshadow_byte SEGS B ARx LAWS)). Qed.

Lemma ev_items_close_holds :
  ev_items_close_spec (fx := fx) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) B ARx SK.
Proof. exact (ev_items_close_holds_zb (alx_zshadow_byte SEGS B ARx LAWS)). Qed.

End w.
