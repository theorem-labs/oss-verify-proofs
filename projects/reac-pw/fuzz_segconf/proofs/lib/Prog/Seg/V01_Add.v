(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain): the piece ADD, [v01_add_stmt] of
   Prog/Seg/V01_Inv.v. From ADD (0x13e64, turn i, v = (p, vid) at sp + 0x40) to JOIN (0x13d74) or, through the -1
   exit 0x13fa0 .. 0x13fac, to TAIL (0x13f04) (plain binary):
     0x13e64 blez s6 (mn <= 0 skips the duplicate loop); 0x13e6c sd s6,0(sp); s6 = mt + 20 mn, s7 = mt; the duplicate
     loop 0x13e80 (V01_Inv.v01_dup_stmt with k = 0, acc = false); 0x13eb0 ld s6,0(sp); bnez s3 -> 0x13ef4 (JOIN, T
     unchanged); 0x13eb8 the cap test (mn >= cap -> 0x13fa0: 0x18(sp) = -1, TAIL with V01_RES = (-1, T)); else
     memcpy(&mt[mn], &v, 20) (memcpy_c.memcpy_contract), s4 = m->n, added + 1 at 0x18(sp), s6 = mn + 1, JOIN with
     T ++ [(p, vid)].
   The model: with g = nth i segs (not ignored, m_split = Some (p, vid)), m_decl_go over skipn i segs makes one step
   ([V01AddPure.decl_step]). The parent string of v comes from mvlan_enc's cstr_enc 16 (CsPure.cstr_bytes); 0 < vid
   <= 4094 from m_split ([V01AddPure.m_split_vid]); the new entry of mt is mtab_enc's append
   ([V01AddPure.mtab_enc_app]); m->n is the u32 at m + 0x2000 of v01_base's mconf_at, carried to the current memory
   by munch (v01a_rd_n).
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_env seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import memcpy_c check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv.
Import ListNotations.
Open Scope Z_scope.

Module V01AddPure.

Lemma cap_rng : forall inp, 0 <= seg_cap inp < 40.
Proof.
  intros inp. unfold seg_cap, seg_pay, SegModel.decode.
  destruct (SegModel.fuzz_u8 (seg_in inp)) as [b0 i1]. destruct (SegModel.fuzz_u8 i1) as [fl i2].
  destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.

Lemma n0_le : forall inp, 0 <= Z.of_nat (length (seg_tab0 inp)) <= seg_cap inp.
Proof.
  intros inp. split; [lia|]. unfold seg_tab0. apply vlan_init_len.
  pose proof (cap_rng inp) as H. unfold seg_cap in H. lia.
Qed.

Lemma skipn_nth_cons : forall {A : Type} (l : list A) (i : nat) (d : A), (i < length l)%nat ->
  skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

(* One turn of m_decl_go on a segment that is not ignored and whose name splits into (p, v). *)
Lemma decl_step : forall segs i T cap a p v,
  (i < length segs)%nat -> ms_ignore (nth i segs mseg_d) = false ->
  m_split (ms_name (nth i segs mseg_d)) = Some (p, v) ->
  m_decl_go (skipn i segs) T cap a =
    if existsb (fun e => (snd e =? v) && (strcmp (fst e) p =? 0)) T then m_decl_go (skipn (S i) segs) T cap a
    else if cap <=? Z.of_nat (length T) then (-1, T)
    else m_decl_go (skipn (S i) segs) (T ++ [(p, v)]) cap (a + 1).
Proof.
  intros segs i T cap a p v Hi Hg Hs. rewrite (skipn_nth_cons segs i mseg_d Hi). cbn [m_decl_go].
  rewrite Hg, Hs. reflexivity.
Qed.

Lemma m_digits_rng : forall l v r, 0 <= v <= 4094 -> m_digits l v = Some r -> 0 <= r <= 4094.
Proof.
  induction l as [|q l IH]; intros v r Hv H; cbn [m_digits] in H.
  - injection H as <-. exact Hv.
  - destruct ((q <? 48) || (57 <? q)) eqn:E1; [discriminate|].
    apply orb_false_iff in E1 as [E1 E2]. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
    destruct (4094 <? v * 10 + (q - 48)) eqn:E3; [discriminate|]. apply Z.ltb_ge in E3.
    eapply IH; [|exact H]. lia.
Qed.

Lemma m_split_vid : forall name p v, m_split name = Some (p, v) -> 0 < v <= 4094.
Proof.
  intros name p v H. unfold m_split in H.
  destruct (strrchr name DOT) as [di|]; [|discriminate].
  destruct ((di =? 0)%nat || (hd0 (skipn (S di) name) =? 0)); [discriminate|].
  destruct (m_digits (skipn (S di) name) 0) as [r|] eqn:E; [|discriminate].
  destruct (r <? 1) eqn:E1; [discriminate|].
  destruct (forallb h_parent_ok (firstn di name)); [|discriminate].
  injection H as <- <-. apply Z.ltb_ge in E1. pose proof (m_digits_rng _ 0 r ltac:(lia) E). lia.
Qed.

Lemma fld_app_l : forall off n (a b : list byte), (off + n <= length a)%nat -> fld off n (a ++ b) = fld off n a.
Proof.
  intros off n a b H. unfold fld. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length a - off))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

(* mt[mn] = v appends (p, vid) to the table mt holds. *)
Lemma mtab_enc_app : forall T bs e f, mtab_enc T bs -> mvlan_enc e f -> mtab_enc (T ++ [e]) (bs ++ f).
Proof.
  intros T bs e f [L H] Hf. pose proof Hf as (Lf & _). split.
  - rewrite !length_app, L, Lf. cbn [length]. lia.
  - intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
    destruct (Nat.lt_ge_cases k (length T)) as [Hl|Hg].
    + rewrite app_nth1 by exact Hl. rewrite fld_app_l by lia. apply H, Hl.
    + assert (Ek : k = length T) by lia. subst k.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      unfold fld. rewrite <- L, skipn_app_exact. rewrite firstn_all2 by lia. exact Hf.
Qed.

(* The parent of v (struct mvlan at A) is a C string sy, zs sy = p. *)
Lemma v_parent : forall segs m A vb p vid, rw_cells segs m A [CB 20 vb] -> mvlan_enc (p, vid) vb ->
  exists sy, bytes_at segs m A (sy ++ [ZERO]) /\ ~ In ZERO sy /\ zs sy = p.
Proof.
  intros segs m A vb p vid [[_ HB] _] (L & Hc & _).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  exact (CsPure.cstr_bytes segs m A vb 16 p HB ltac:(lia) Hc).
Qed.

(* A free CB cell split into its first k bytes and the rest. *)
Lemma cb_split2 : forall segs m A n k bs, rw_cells segs m A [CB n bs] -> (k <= n)%nat ->
  rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros segs m A n k bs [[Hwf Hb] Hw] Hk. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb as [H1 H2].
  rewrite length_firstn, Nat.min_l in H2 by lia.
  destruct Hw as (Hw0 & Hw1 & Hw).
  unfold rw_cells, cells_at, wr_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite !app_nil_r, !Nat.add_0_r.
  split; split; [split| |split|].
  - split; [rewrite length_firstn; lia | exact I].
  - exact H1.
  - split; [lia|]. split; [lia|]. intros j Hj. apply Hw. lia.
  - split; [rewrite length_skipn; lia | exact I].
  - exact H2.
  - split; [lia|]. split; [lia|]. intros j Hj.
    replace (A + Z.of_nat k + j) with (A + (Z.of_nat k + j)) by lia. apply Hw. lia.
Qed.

Lemma rw_cb_eq : forall segs m A A' n n' bs, rw_cells segs m A [CB n bs] -> A = A' -> n = n' ->
  rw_cells segs m A' [CB n' bs].
Proof. intros; subst; assumption. Qed.

Lemma bytes_at_eq' : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

(* Main's nine frame cells, value by value. *)
Lemma fr_eq : forall segs m A (x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 : word),
  rw_cells segs m A [C8 x0; C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C4 x7; C4 x8] ->
  x0 = y0 -> x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 ->
  rw_cells segs m A [C8 y0; C8 y1; C8 y2; C8 y3; C8 y4; C8 y5; C8 y6; C4 y7; C4 y8].
Proof. intros; subst; assumption. Qed.

(* `bge` on two non-negative words below 2^63. *)
Lemma lts_lit : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor. rewrite !unsigned_lit by lia.
  rewrite !zb_lxor_sign by lia. rewrite !Z.mod_small by lia.
  apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.

End V01AddPure.

(* ---- The plain image: states, memory transport, m->n ---- *)

Lemma v01a_evt_eq : forall (Q : machine_state -> Prop) ms ms', evt rsegs Q ms' -> ms' = ms -> evt rsegs Q ms.
Proof. intros Q ms ms' H ->. exact H. Qed.

Lemma v01a_ms_eq : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23
    y24 y25 y26 y27 y28 y29 y30 y31 : word) (F : bvmap 5 word) (pc : word) (fc : bv 32) m ro,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 -> x9 = y9 ->
  x10 = y10 -> x11 = y11 -> x12 = y12 -> x13 = y13 -> x14 = y14 -> x15 = y15 -> x16 = y16 -> x17 = y17 ->
  x18 = y18 -> x19 = y19 -> x20 = y20 -> x21 = y21 -> x22 = y22 -> x23 = y23 -> x24 = y24 -> x25 = y25 ->
  x26 = y26 -> x27 = y27 -> x28 = y28 -> x29 = y29 -> x30 = y30 -> x31 = y31 ->
  MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
        x29 x30 x31) F pc fc None m ro =
  MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
        y29 y30 y31) F pc fc None m ro.
Proof. intros; subst; reflexivity. Qed.

(* Two words of the run that are equal as integers mod 2^64 (addiw's sign-extension, `mul`/`add` of the table
   address, m->n read with `lw`). *)
Ltac v01a_weq :=
  apply Z_to_bv_eqm; unfold sx32, MVLAN_SIZE, b2z; cbv beta iota;
  rewrite ?length_app; cbn [length];
  rewrite ?unsigned_lit_wrap; unfold bv_swrap, bv_wrap;
  try change (bv_half_modulus 32) with 2147483648; try change (bv_modulus 32) with 4294967296;
  Z.div_mod_to_equations; lia.

Ltac v01a_req :=
  lazymatch goal with
  | |- ?a = ?a => reflexivity
  | |- ?a = ?b => first [ is_evar a; reflexivity | is_evar b; reflexivity | v01a_weq ]
  end.

Ltac v01a_sub :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in Hx |- *; unfold MT_N, MVLAN_SIZE, v_cap in *;
  repeat split; intro; lia.

(* A branch: K the condition, in integers. *)
Ltac v01a_kz K :=
  rewrite ?V01AddPure.lts_lit in K by lia;
  zify_cond K;
  try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
         ?Z.eqb_neq in K).
Ltac v01a_tkn := let K := fresh "K" in if_cases K; [v01a_kz K | v01a_kz K; exfalso; lia].
Ltac v01a_ntk := let K := fresh "K" in if_cases K; [v01a_kz K; exfalso; lia | v01a_kz K].

Ltac v01a_mem_name m := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => rename M into m end.

(* v01_mem survives a run that writes only main's frame cells and mt. *)
Lemma v01a_mem_tr : forall inp S c mm tab mt m0 m m' W,
  v01_geo inp S c mm tab mt -> v01_mem inp S tab mt m0 m ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  sub_fp W [(S - 208, S - 144); (mt, mt + MT_N inp)] ->
  v01_mem inp S tab mt m0 m'.
Proof.
  intros inp S c mm tab mt m0 m m' W GEO (MU & WM & _ & ST & (bs & HB & ENC) & (fr & FREE) & GU) MU' WM' MI' SUB.
  pose proof GEO as (_ & HSlo & HS47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htab & HtabS & _ & _ & Hmt & HmtS & _ &
                     _ & _ & _ & _ & _ & _ & Atm).
  pose proof (V01AddPure.cap_rng inp) as HC. pose proof (V01AddPure.n0_le inp) as HN.
  pose proof (proj1 ENC) as HBL.
  unfold TAB_N, MT_N, RVLAN_SIZE, MVLAN_SIZE, apart, v_cap, v_n0, v_tab0 in *.
  assert (MUL : munch [(S - 208, S - 144); (mt, mt + 20 * (seg_cap inp + 1))] m m')
    by (apply (munch_weaken W); assumption).
  unfold v01_mem. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (munch_trans _ m0 m m' MU).
    apply (munch_weaken [(S - 208, S - 144); (mt, mt + 20 * (seg_cap inp + 1))] _ m m'); [|exact MUL].
    intros x Hx. unfold v01_W, MT_N, TAB_N, MVLAN_SIZE, RVLAN_SIZE in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & H3 & _). split; [lia | split; [lia | exact I]].
  - exact (wmono_trans rsegs _ _ _ WM WM').
  - exact MI'.
  - apply (stk_transport_disjoint rsegs _ m m' _ _ ST MUL WM'). cbn [disjoint_from].
    split; [lia | split; [lia | exact I]].
  - exists bs. split; [|exact ENC]. apply (bytes_at_transport rsegs _ m m' _ _ HB MUL). cbn [disjoint_from].
    split; [lia | split; [lia | exact I]].
  - exists fr. apply (rw_cells_transport rsegs _ m m' _ _ FREE MUL WM'). cbn [disjoint_from cells_size csize].
    split; [lia | split; [lia | exact I]].
  - unfold guard_at, RVLAN_SIZE in *. apply (bytes_at_transport rsegs _ m m' _ _ GU MUL).
    change (length GUARD_BYTES) with 18%nat. cbn [disjoint_from].
    split; [lia | split; [lia | exact I]].
Qed.

(* v01_mt survives a run that writes only main's frame cells. *)
Lemma v01a_mt_tr : forall inp S c mm tab mt T m m' W,
  v01_geo inp S c mm tab mt -> v01_mt inp mt T m ->
  munch W m m' -> wmono rsegs m m' -> sub_fp W [(S - 208, S - 144)] ->
  v01_mt inp mt T m'.
Proof.
  intros inp S c mm tab mt T m m' W GEO (HL & (bs & HB & ENC) & (fr & FREE)) MU WM SUB.
  pose proof GEO as (_ & HSlo & HS47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & HmtS & _).
  pose proof (proj1 ENC) as HBL.
  unfold MT_N, MVLAN_SIZE, v_cap in *.
  assert (MUL : munch [(S - 208, S - 144)] m m') by (apply (munch_weaken W); assumption).
  unfold v01_mt. split; [exact HL|]. split.
  - exists bs. split; [|exact ENC]. apply (bytes_at_transport rsegs _ m m' _ _ HB MUL). cbn [disjoint_from].
    split; [lia | exact I].
  - exists fr. apply (rw_cells_transport rsegs _ m m' _ _ FREE MUL WM). cbn [disjoint_from cells_size csize].
    split; [lia | exact I].
Qed.

(* m->n (the u32 at m + 0x2000) in any memory the run reaches. *)
Lemma v01a_rd_n : forall inp S c mm tab mt m0 m,
  v01_geo inp S c mm tab mt -> v01_base inp c mm m0 -> munch (v01_W inp S tab mt) m0 m ->
  ov_read_bytes rsegs m (wa (mm + 8192)) 4 = Some (le4 (Z_to_bv 64 (v_nsegs inp))) /\ 0 <= v_nsegs inp <= 32.
Proof.
  intros inp S c mm tab mt m0 m GEO (_ & (bs & HB & ENC) & _) MU.
  pose proof GEO as (_ & HSlo & HS47 & _ & _ & _ & _ & _ & Hm & HmS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & Atab & Amt & _).
  pose proof ENC as (HL & H32 & _ & HN & _).
  unfold SEG_M_SIZE, apart in *.
  assert (HB' : bytes_at rsegs m mm bs).
  { apply (bytes_at_transport rsegs _ m0 m _ _ HB MU). unfold v01_W. cbn [disjoint_from].
    split; [lia | split; [lia | split; [lia | exact I]]]. }
  split.
  - exact (CsPure.cs_rd4 rsegs m mm bs 8192 _ HB' ltac:(lia) ltac:(lia) HN).
  - unfold v_nsegs, v_segs. lia.
Qed.

(* ---- The piece ---- *)
Lemma v01_add : memcpy_contract -> v01_dup_stmt -> v01_add_stmt.
Proof.
  intros MC DUP. unfold v01_add_stmt, K_add_at.
  intros inp S c mm tab mt m0 gp tp F fc Q i GEO BASE KJ KT
    T added p vid ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 t3 t4 t5 t6 m
    (Hi & (MA & MB) & IGN & SPL & MEM & MT & (w00 & w38 & FR) & (vb & VC & VE)).
  pose proof GEO as (_ & HSlo & HS47 & _ & _ & _ & _ & _ & Hmm & HmmS & _ & _ & Htab & HtabS & _ & _ &
                     Hmt & HmtS0 & _).
  assert (HmtS : mt + 20 * (v_cap inp + 1) <= S - 65536)
    by (unfold v_cap; unfold MT_N, MVLAN_SIZE in HmtS0; lia).
  clear HmtS0.
  assert (HCAP : 0 <= v_cap inp < 40) by (unfold v_cap; apply V01AddPure.cap_rng).
  assert (HN0 : 0 <= v_n0 inp <= v_cap inp) by (unfold v_n0, v_tab0, v_cap; apply V01AddPure.n0_le).
  pose proof (V01AddPure.m_split_vid _ _ _ SPL) as HVID.
  pose proof (proj1 MT) as HTL.
  pose proof (proj1 VE) as HVBL.
  (* 0x13eb8: the cap test, with mn = length T and no duplicate in T *)
  assert (C : forall (mA : word -> option byte) (ra' a0' a1' a2' a3' s3' s7' w00' : word),
    existsb (fun e => (snd e =? vid) && (strcmp (fst e) p =? 0)) T = false ->
    v01_mem inp S tab mt m0 mA -> v01_mt inp mt T mA ->
    v01_frame S w00' (Z_to_bv 64 tab) (Z_to_bv 64 (v_cap inp)) (Z_to_bv 64 added) (Z_to_bv 64 mt)
      (Z_to_bv 64 V01_MASK) (Z_to_bv 64 c) w38 (Z_to_bv 64 (v_n0 inp)) mA ->
    rw_cells rsegs mA (S - 208 + 64) [CB 20 vb] ->
    evt rsegs Q (vst 0x13eb8 ra' (Z_to_bv 64 (S - 208)) gp tp t0 t1 t2 (Z_to_bv 64 mm)
      (Z_to_bv 64 (mm + 256 * Z.of_nat i)) a0' a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat i)) s3'
      (Z_to_bv 64 (v_nsegs inp)) (Z_to_bv 64 vid) (Z_to_bv 64 (Z.of_nat (length T))) s7' (Z_to_bv 64 4094)
      (Z_to_bv 64 (- (mm + 256 * Z.of_nat i))) (Z_to_bv 64 (mm + 0x2000)) (Z_to_bv 64 (-10)) t3 t4 t5 t6 F fc mA)).
  { intros mA ra' a0' a1' a2' a3' s3' s7' w00' EX VM VT FRA VCA.
    pose proof (proj1 (proj2 (proj2 VM))) as MIA.
    destruct VT as (HTL' & (bsT & HBT & ENC) & (fr & FREE)).
    pose proof (proj1 ENC) as HBTL.
    unfold MVLAN_SIZE in FREE.
    unfold v01_frame in FRA.
    pose proof (munch_refl [(S - 208, S - 144); (mt, mt + MT_N inp)] mA) as MU.
    pose proof (wmono_refl rsegs mA) as WM.
    unfold vst.
    (* 0x13eb8 ld a0,0x10(sp); 0x13ebc bge s6,a0 *)
    zstep. zstep.
    destruct (Z_lt_le_dec (Z.of_nat (length T)) (v_cap inp)) as [HLT|HGE].
    - (* append: 0x13ec0 addiw s3,s6,1; 0x13ec4 .. 0x13ed8 a0 = mt + 20 mn, a1 = sp + 0x40, a2 = 20;
         0x13edc jal memcpy *)
      v01a_ntk.
      do 8 zstep.
      destruct (V01AddPure.cb_split2 rsegs mA (mt + 20 * Z.of_nat (length T)) _ 20 fr FREE ltac:(lia))
        as (DST & REST).
      clear FREE.
      assert (VB : bytes_at rsegs mA (S - 208 + 64) vb).
      { destruct VCA as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
      eapply evt_cut; [eapply MC with (src := vb) (junk := firstn 20 fr) | ].
      + rewrite unsigned_lit by lia. exact VB.
      + rewrite HVBL. reflexivity.
      + rewrite !unsigned_lit by lia.
        replace (mt + Z.of_nat (length T) * 20) with (mt + 20 * Z.of_nat (length T)) by lia. exact DST.
      + rewrite !unsigned_lit by lia. lia.
      + exact MIA.
      + intros ms' (t0' & t1' & t2' & a1'' & a2'' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 &
                    -> & MU3 & WM3 & MI3 & RW3 & BA3).
        rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit in RW3 by lia.
        rewrite !unsigned_lit in BA3 by lia.
        replace (mt + Z.of_nat (length T) * 20) with (mt + 20 * Z.of_nat (length T)) in MU3 by lia.
        replace (mt + Z.of_nat (length T) * 20) with (mt + 20 * Z.of_nat (length T)) in RW3 by lia.
        change (Z.to_nat 20) with 20%nat in RW3.
        rewrite ret_pc_even by (try lia; reflexivity).
        assert (SUB3 : sub_fp [(mt + 20 * Z.of_nat (length T), mt + 20 * Z.of_nat (length T) + 20)]
                         [(S - 208, S - 144); (mt, mt + MT_N inp)]) by v01a_sub.
        pose proof (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB3 MU3)) as MU'. clear MU. rename MU' into MU.
        pose proof (wmono_trans rsegs _ _ _ WM WM3) as WM'. clear WM. rename WM' into WM.
        apply (bytes_at_transport rsegs [(mt + 20 * Z.of_nat (length T), mt + 20 * Z.of_nat (length T) + 20)] mA m3 _ _) in HBT;
          [| exact MU3 | cbn [disjoint_from]; split; [lia | exact I]].
        apply (rw_cells_transport rsegs [(mt + 20 * Z.of_nat (length T), mt + 20 * Z.of_nat (length T) + 20)] mA m3 _ _) in REST;
          [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [lia | exact I]].
        apply (rw_cells_transport rsegs [(mt + 20 * Z.of_nat (length T), mt + 20 * Z.of_nat (length T) + 20)] mA m3 _ _) in FRA;
          [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [lia | exact I]].
        apply (rw_cells_transport rsegs [(mt + 20 * Z.of_nat (length T), mt + 20 * Z.of_nat (length T) + 20)] mA m3 _ _) in VCA;
          [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize]; split; [lia | exact I]].
        clear MIA DST VB SUB3.
        assert (VM3 : v01_mem inp S tab mt m0 m3)
          by (apply (v01a_mem_tr inp S c mm tab mt m0 mA m3 _ GEO VM MU WM MI3); v01a_sub).
        destruct (v01a_rd_n inp S c mm tab mt m0 m3 GEO BASE (proj1 VM3)) as (HR3 & HNS).
        clear VM3 MU3 WM3.
        (* 0x13ee0 lw s4,0(s10); 0x13ee4 ld a0,0x18(sp); 0x13ee8 addiw a0,a0,1; 0x13eec sd a0,0x18(sp);
           0x13ef0 mv s6,s3; 0x13ef4 ld s3,8(sp); 0x13ef8 j JOIN *)
        do 7 zstep.
        v01a_mem_name m4.
        eapply v01a_evt_eq; [eapply (KJ (T ++ [(p, vid)]) (added + 1)) | apply v01a_ms_eq; v01a_req].
        unfold v01_loop_mem. split; [exact Hi|]. split.
        { split; [rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat]; lia|].
          rewrite (V01AddPure.decl_step _ _ _ _ _ _ _ Hi IGN SPL), EX, (proj2 (Z.leb_gt _ _) HLT) in MB.
          exact MB. }
        split; [apply (v01a_mem_tr inp S c mm tab mt m0 mA m4 _ GEO VM MU WM MI3); v01a_sub|].
        split.
        { split; [rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat]; lia|]. split.
          - exists (bsT ++ vb). split; [|exact (V01AddPure.mtab_enc_app _ _ _ _ ENC VE)].
            apply bytes_at_app. split; [exact HBT|].
            destruct RW3 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
            eapply V01AddPure.bytes_at_eq'; [exact HB | rewrite HBTL; lia].
          - exists (skipn 20 fr). eapply V01AddPure.rw_cb_eq; [exact REST | |].
            + rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat Pos.of_succ_nat]. unfold MVLAN_SIZE. lia.
            + rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat Pos.of_succ_nat]. unfold MVLAN_SIZE. lia. }
        split.
        { do 3 eexists. unfold v01_frame. eapply V01AddPure.fr_eq; [exact FRA | v01a_req ..]. }
        exists vb. exact VCA.
    - (* the -1 exit: 0x13fa0 li a0,-1; 0x13fa4 sd a0,0x18(sp); 0x13fa8 ld s3,8(sp); 0x13fac j TAIL *)
      v01a_tkn.
      do 4 zstep.
      v01a_mem_name mE.
      assert (HRES : V01_RES inp = (-1, T)).
      { rewrite <- MB, (V01AddPure.decl_step _ _ _ _ _ _ _ Hi IGN SPL), EX.
        rewrite (proj2 (Z.leb_le _ _) HGE). reflexivity. }
      assert (EL : Z.of_nat (length T) = Z.of_nat (length (snd (V01_RES inp)))) by (rewrite HRES; reflexivity).
      rewrite EL.
      eapply KT.
      unfold v01_tail_mem. rewrite HRES. cbn [fst snd].
      split; [|split].
      + apply (v01a_mem_tr inp S c mm tab mt m0 mA mE _ GEO VM MU WM MIA). v01a_sub.
      + split; [exact HTL'|]. split; [exists bsT; split; assumption | exists fr; exact FREE].
      + replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in FRA
          by (apply Z_to_bv_eqm; reflexivity).
        exists w00', (Z_to_bv 64 tab), (Z_to_bv 64 V01_MASK), w38. exact FRA. }
  unfold v01_add_st, vst.
  (* 0x13e64 blez s6 *)
  zstep.
  destruct (Nat.eq_dec (length T) 0) as [HL0|HL0].
  - (* mn = 0: to 0x13eb8 *)
    v01a_tkn.
    assert (EX0 : existsb (fun e => (snd e =? vid) && (strcmp (fst e) p =? 0)) T = false)
      by (destruct T; [reflexivity | cbn [length] in HL0; lia]).
    exact (C m ra a0 a1 a2 a3 s3 s7 w00 EX0 MEM MT FR VC).
  - (* 0x13e68 li s3,0; 0x13e6c sd s6,0(sp); 0x13e70 .. 0x13e7c s6 = mt + 20 mn, s7 = mt *)
    v01a_ntk.
    pose proof (proj1 (proj2 (proj2 MEM))) as MI.
    unfold v01_frame in FR.
    pose proof (munch_refl [(S - 208, S - 144)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    do 6 zstep.
    v01a_mem_name m2.
    assert (VM2 : v01_mem inp S tab mt m0 m2).
    { apply (v01a_mem_tr inp S c mm tab mt m0 m m2 _ GEO MEM MU WM MI). v01a_sub. }
    assert (VT2 : v01_mt inp mt T m2).
    { apply (v01a_mt_tr inp S c mm tab mt T m m2 _ GEO MT MU WM). v01a_sub. }
    clear MEM MT MU WM.
    destruct (V01AddPure.v_parent rsegs m2 (S - 208 + 64) vb p vid VC VE) as (sy & HSY & NSY & ZSY).
    (* the duplicate loop 0x13e80 at k = 0, acc = false *)
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (b2z false)) by reflexivity.
    replace (Z_to_bv 64 (mt + Z.of_nat (length T) * 20))
      with (Z_to_bv 64 (mt + MVLAN_SIZE * Z.of_nat (length T))) by (unfold MVLAN_SIZE; f_equal; lia).
    replace (Z_to_bv 64 mt) with (Z_to_bv 64 (mt + MVLAN_SIZE * Z.of_nat 0)) by (unfold MVLAN_SIZE; f_equal; lia).
    eapply (DUP Q m2 mt (S - 208) vid T sy 0%nat false).
    + exact (proj1 (proj2 VT2)).
    + lia.
    + lia.
    + unfold MVLAN_SIZE. lia.
    + lia.
    + lia.
    + exact HSY.
    + exact NSY.
    + exact HVID.
    + intros ra' a0' a1' a2' a3' s7'. unfold vst.
      change (skipn 0 T) with T. rewrite Bool.orb_false_l, ZSY.
      destruct (existsb (fun e => (snd e =? vid) && (strcmp (fst e) p =? 0)) T) eqn:EX; cbn [b2z].
      * (* a duplicate: 0x13eb0 ld s6,0(sp); 0x13eb4 bnez s3; 0x13ef4 ld s3,8(sp); 0x13ef8 j JOIN *)
        zstep. zstep. v01a_tkn. zstep. zstep.
        eapply (KJ T added).
        unfold v01_loop_mem. split; [exact Hi|]. split.
        { split; [exact MA|]. rewrite (V01AddPure.decl_step _ _ _ _ _ _ _ Hi IGN SPL), EX in MB. exact MB. }
        split; [exact VM2|]. split; [exact VT2|]. split.
        { exists (Z_to_bv 64 (Z.of_nat (length T))), (Z_to_bv 64 tab), w38. exact FR. }
        exists vb. exact VC.
      * (* none: 0x13eb0 ld s6,0(sp); 0x13eb4 bnez s3 falls to 0x13eb8 *)
        zstep. zstep. v01a_ntk.
        eapply (C m2); [reflexivity | exact VM2 | exact VT2 | exact FR | exact VC].
Qed.
