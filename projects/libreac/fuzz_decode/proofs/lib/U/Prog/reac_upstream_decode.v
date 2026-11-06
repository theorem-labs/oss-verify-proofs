From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import reac_frame_inspect_c reac_decode_c
  reac_upstream_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Lemma braid_byte_at' : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold braid_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

Lemma up_ok_true : forall raw out len bs, up_ok raw out len bs = true <->
  raw <> 0 /\ out <> 0 /\ 0 <= up_nch len /\ inspect_byte bs 12 = 0x88 /\ inspect_byte bs 13 = 0x19 /\
  inspect_byte bs (Z.to_nat (len - 2)) = 0xC2 /\ inspect_byte bs (Z.to_nat (len - 1)) = 0xEA.
Proof.
  intros. unfold up_ok. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq, !Z.eqb_eq, Z.leb_le. tauto.
Qed.

Lemma up_nch_pos : forall len, 0 <= up_nch len ->
  124 <= len /\ (len - 52) mod 36 = 0 /\ ((len - 52) / 36) mod 2 = 0 /\ (len - 52) / 36 <= 40 /\
  up_nch len = (len - 52) / 36.
Proof.
  intros len H. unfold up_nch in *.
  destruct ((124 <=? len) && ((len - 52) mod 36 =? 0) && (((len - 52) / 36) mod 2 =? 0) && ((len - 52) / 36 <=? 40)) eqn:E.
  - rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq in E. tauto.
  - lia.
Qed.

Lemma up_nch_val : forall len, 124 <= len -> (len - 52) mod 36 = 0 -> ((len - 52) / 36) mod 2 = 0 ->
  (len - 52) / 36 <= 40 -> up_nch len = (len - 52) / 36.
Proof.
  intros len H1 H2 H3 H4. unfold up_nch.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.eqb_eq _ _) H2), (proj2 (Z.eqb_eq _ _) H3), (proj2 (Z.leb_le _ _) H4).
  reflexivity.
Qed.

Lemma div36 : forall x, 0 <= x < 2^64 -> Z.shiftr (Z.shiftr (x * 16397105843297379215) 64) 5 = x / 36.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
  pose proof (Z.div_mod x 36 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 36 ltac:(lia)) as B.
  symmetry. apply (Z.div_unique _ _ _ (28 * (x / 36) + (x mod 36) * 16397105843297379215)).
  - left. split; [lia|]. cbn. lia.
  - cbn. lia.
Qed.

Lemma width_test : forall q, 0 <= q < 2^31 ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (q + -41))) (Z_to_bv 64 (-39)) = negb ((2 <=? q) && (q <=? 40)).
Proof.
  intros q Hq. rewrite swrap32_id by lia. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z_lt_le_dec q 41).
  - rewrite <- (Z.mod_add (q + -41) 1) by lia. rewrite Z.mod_small by lia.
    change (-39 mod 2^64) with 18446744073709551577.
    destruct (Z.leb_spec 2 q); destruct (Z.leb_spec q 40); destruct (Z.ltb_spec (q + -41 + 1 * 2^64) 18446744073709551577);
      cbn; try reflexivity; lia.
  - rewrite Z.mod_small by lia. change (-39 mod 2^64) with 18446744073709551577.
    destruct (Z.leb_spec 2 q); destruct (Z.leb_spec q 40); destruct (Z.ltb_spec (q + -41) 18446744073709551577);
      cbn; try reflexivity; lia.
Qed.

Lemma eqb_zxb : forall (b : byte) c, 0 <= c < 2^64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb. unfold zxb, bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Definition up_boff (p k : Z) : Z :=
  if p =? 0 then (if k =? 0 then 3 else if k =? 1 then 0 else 1)
  else (if k =? 0 then 4 else if k =? 1 then 5 else 2).

Section UP.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw out len lo : Z).

Definition PostU : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if up_ok raw out len bs then 12 else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if up_ok raw out len bs
     then munch [(bv_unsigned sp - 48, bv_unsigned sp); (out, out + 36 * up_nch len)] m m' /\
          bytes_at rsegs m' out (braid_out bs (up_nch len) 12)
     else munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FRU mk junk := (rw_cells rsegs mk (bv_unsigned sp + -48) [CB 24 junk; C8 s2; C8 s1; C8 s0]).
Local Notation STATE pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 :=
  (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
        s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 48 <= SP.
Hypothesis Hlo : 0 <= lo.

Lemma up_exit : forall (m1 : word -> option byte) (r : Z) (junk : list byte)
    (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  FRU m1 junk -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 ->
  r = (if up_ok raw out len bs then 12 else -1) ->
  (if up_ok raw out len bs
   then munch [(SP + -48, SP); (out, out + 36 * up_nch len)] m m1 /\
        bytes_at rsegs m1 out (braid_out bs (up_nch len) 12)
   else munch [(SP + -48, SP)] m m1) ->
  evt rsegs PostU (STATE 0x13f6c m1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31).
Proof.
  intros m1 r junk x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 5 step.
  apply evt_done. unfold PostU. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -48) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -48 + Z.of_nat 48) with SP in ST2 by lia. exact ST2.
  - replace (SP - 48) with (SP + -48) by lia. exact HM.
Qed.

Lemma up_fail : forall (m1 : word -> option byte) (junk : list byte)
    (x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  FRU m1 junk -> stk rsegs m1 lo (SP + -48) -> wmono rsegs m m1 -> munch [(SP + -48, SP)] m m1 ->
  up_ok raw out len bs = false ->
  evt rsegs PostU (STATE 0x13f6c m1 x5 x6 x7 x8 x9 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31).
Proof.
  intros m1 junk x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 HF ST WM MU E.
  eapply up_exit; [exact HF | exact ST | exact WM | rewrite E; reflexivity | rewrite E; exact MU].
Qed.

Variable nch : Z.
Hypothesis Hnchdef : up_nch len = nch.
Hypothesis Hnch : 2 <= nch <= 40.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hlen52 : len = 52 + 36 * nch.
Hypothesis Hlen : length bs = Z.to_nat len.
Hypothesis Hraw : 0 < raw.
Hypothesis Hraw2 : raw + len <= 2^64.
Hypothesis Hout : 0 < out.
Hypothesis HoutN : out + 36 * nch < 2^64.
Definition UPSEP : Prop :=
  (out + 36 * nch <= raw \/ raw + len <= out) /\ (out + 36 * nch <= SP + -48 \/ SP <= out) /\
  (raw + len <= SP + -48 \/ SP <= raw).
Hypothesis HSEP : UPSEP.
Hypothesis OK : up_ok raw out len bs = true.

Local Notation N := (36 * nch).

Definition up_pre (j : Z) : list byte := map (braid_byte bs nch 12) (map Z.of_nat (seq 0 (Z.to_nat j))).

Lemma up_pre_len : forall j, 0 <= j -> Z.of_nat (length (up_pre j)) = j.
Proof. intros j Hj. unfold up_pre. rewrite length_mapseq. lia. Qed.

Lemma up_pre_S : forall j, 0 <= j -> up_pre (j + 1) = up_pre j ++ [braid_byte bs nch 12 j].
Proof.
  intros j Hj. unfold up_pre. replace (Z.to_nat (j + 1)) with (Z.to_nat j + 1)%nat by lia.
  rewrite seq_app, !map_app. cbn [seq map Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma up_bw_ext : forall mk q0 q, bytes_at rsegs mk out (up_pre q0) -> q0 = q -> 0 <= q -> out + q + 1 <= 2^64 ->
  bytes_at rsegs (write_to_mem mk (wa (out + q)) [braid_byte bs nch 12 q]) out (up_pre (q + 1)).
Proof.
  intros mk q0 q HB E Hq Hb. subst q0. pose proof (up_pre_len q Hq) as L.
  rewrite up_pre_S by lia. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | cbn [length]; lia].
  - rewrite L. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Definition INVU (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ (exists junk, FRU mk junk) /\ stk rsegs mk lo (SP + -48) /\ wr_at rsegs mk out N /\
  munch [(SP + -48, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\ bytes_at rsegs mk out (up_pre j).

Lemma INVU_idx : forall mk j j', INVU mk j -> j = j' -> INVU mk j'.
Proof. intros; subst; assumption. Qed.

Lemma UBR_rd : forall mk ch s k o, bytes_at rsegs mk raw bs -> 0 <= ch < nch -> 0 <= s < 12 -> 0 <= k < 3 ->
  o = up_boff (ch mod 2) k ->
  ov_read_bytes rsegs mk (Z_to_bv 64 (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o)))) 1 =
  Some [braid_byte bs nch 12 (3 * (ch * 12 + s) + k)].
Proof.
  intros mk ch s k o HB Hch Hs Hk Ho. rewrite braid_byte_at' by lia.
  assert (Ep : braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) + o).
  { unfold braid_pos, up_boff in *. cbv zeta. subst o. destruct (ch mod 2 =? 0), (k =? 0), (k =? 1); lia. }
  rewrite Ep.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= 11 * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= o <= 5) by (unfold up_boff in Ho; subst o; destruct (ch mod 2 =? 0), (k =? 0), (k =? 1); lia).
  apply rd1; [exact HB|]. rewrite Hlen, Z2Nat.id by lia. nia.
Qed.

Ltac stf :=
  let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
  pose proof HSEP as [D1 [D2 D3]]; st; clear D1 D2 D3.

Ltac ostore :=
  rewrite ?le1_zxb;
  lazymatch goal with
  | |- evt ?sg ?Q (MS ?R ?Fr ?pc ?f ?rv (write_to_mem ?mk ?w [?b]) ?ro) =>
      let a := addr_expr w in
      lazymatch a with
      | out + ?q =>
          change (evt sg Q (MS R Fr pc f rv (write_to_mem mk (wa (out + q)) [b]) ro));
          match goal with BW : bytes_at _ mk out (up_pre ?q0) |- _ =>
            apply (up_bw_ext mk q0 q) in BW; [ | lia | lia | lia ]
          end;
          match goal with H : Z.of_nat (length (up_pre _)) = _ |- _ => clear H end;
          assert (LB : Z.of_nat (length (up_pre (q + 1))) = q + 1) by (apply up_pre_len; lia);
          let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
          pose proof HSEP as [D1 [D2 D3]];
          transport_chunks sg mk (out + q) [b]; footprint_after_store sg mk (out + q) [b];
          clear D1 D2 D3;
          let m2 := fresh "m" in set (m2 := write_to_mem mk (wa (out + q)) [b]) in *; clearbody m2
      end
  end.

Ltac rebundle :=
  lazymatch goal with H : rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?c3 :: ?post) |- _ =>
    apply (rw_cells_merge rsegs mm A [] [c1; c2; c3] post) in H; cbn [app cells_size csize Nat.add] in H;
    split; [assumption|]; split; [eexists; exact H|]; split; [assumption|]; split; [assumption|];
    split; [assumption|]; split; [assumption|]; eassumption
  end.

Lemma up_inner : forall (ch : Z) (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x30 x31 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = 12 -> bv_unsigned x6 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x7 = 2147483646 -> bv_unsigned x10 = ch -> bv_unsigned x11 = raw + 50 ->
  bv_unsigned x13 = nch -> bv_unsigned x14 = 18446744073709551608 -> bv_unsigned x15 = SP + -48 ->
  bv_unsigned x16 = 18446744073709551599 -> bv_unsigned x17 = 18446744073709551615 ->
  bv_unsigned x28 = 18446744073709551607 -> bv_unsigned x30 = ch - ch mod 2 -> bv_unsigned x31 = ch mod 2 ->
  (forall (m2 : word -> option byte) (y8 y9 y12 y18 y29 : word),
     bv_unsigned y8 = out + 3 * (ch * 12 + 11) -> INVU m2 (3 * (ch * 12 + 12)) ->
     evt rsegs PostU (STATE 0x140f8 m2 x5 x6 x7 y8 y9 x10 x11 y12 x13 x14 x15 x16 x17 y18 x28 y29 x30 x31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x9 x12 x18 x29 : word),
  Z.to_nat (12 - s) = K -> 0 <= s < 12 ->
  bv_unsigned x29 = s -> bv_unsigned x12 = out + 3 * (ch * 12 + s) ->
  INVU m1 (3 * (ch * 12 + s)) ->
  evt rsegs PostU (STATE 0x14034 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31).
Proof.
  intros ch x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x30 x31
    Hch H5 H6 H7 H10 H11 H13 H14 H15 H16 H17 H28 H30 H31 CONT K.
  apply wv in H5, H6, H7, H10, H11, H13, H14, H15, H16, H17, H28, H30, H31.
  subst x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x30 x31.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (ch * 12 <= (nch - 1) * 12) by nia.
  pose proof (u64_range sp) as Rsp.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x9 x12 x18 x29 HK Hs H29 H12 I0.
  assert (s * nch <= 11 * nch) by nia.
  assert (0 <= s * nch) by nia.
  apply wv in H29, H12. subst x29 x12.
  destruct I0 as (BR & (junk & FR) & ST & WA & MU & WM & BW).
  assert (LB : Z.of_nat (length (up_pre (3 * (ch * 12 + s)))) = 3 * (ch * 12 + s)) by (apply up_pre_len; lia).
  st. st. st. cnd false.
  st. st. st. st. st. cnd false.
  st. st. st.
  st.
  destruct (Z.eqb_spec (ch mod 2) 0) as [EP|EP].
  - cnd false.
    st. stf. st. cnd false.
    stf. st. cnd false.
    st. st.
    stf. st. cnd false.
    st. cnd false.
    st.
    pose proof (UBR_rd _ ch s 0 3 BR Hch Hs ltac:(lia) ltac:(rewrite EP; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (UBR_rd _ ch s 1 0 BR Hch Hs ltac:(lia) ltac:(rewrite EP; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (UBR_rd _ ch s 2 1 BR Hch Hs ltac:(lia) ltac:(rewrite EP; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. st. clear HR HS. ostore.
    st. st.
    brq BR'.
    + eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INVU_idx; [rebundle | lia]].
    + eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1));
        [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
        | eapply INVU_idx; [rebundle | lia] ].
  - assert (E1 : ch mod 2 = 1) by lia. clear EP.
    cnd true.
    st. stf. st. cnd false.
    st. stf. st. cnd false.
    st.
    stf. st. cnd false.
    st. cnd false.
    st.
    pose proof (UBR_rd _ ch s 0 4 BR Hch Hs ltac:(lia) ltac:(rewrite E1; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (UBR_rd _ ch s 1 5 BR Hch Hs ltac:(lia) ltac:(rewrite E1; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (UBR_rd _ ch s 2 2 BR Hch Hs ltac:(lia) ltac:(rewrite E1; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * 12 + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. st. clear HR HS. ostore.
    st. st.
    brq BR'.
    + eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INVU_idx; [rebundle | lia]].
    + eapply (IH (Z.to_nat (12 - (s + 1))) ltac:(lia) (s + 1));
        [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
        | eapply INVU_idx; [rebundle | lia] ].
Qed.

Lemma up_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 12 -> bv_unsigned x6 = 18446744073709551615 - (raw + 50) -> bv_unsigned x7 = 2147483646 ->
  bv_unsigned x10 = ch -> bv_unsigned x11 = raw + 50 -> bv_unsigned x12 = out + 3 * (ch * 12) ->
  bv_unsigned x13 = nch -> bv_unsigned x14 = 18446744073709551608 -> bv_unsigned x15 = SP + -48 ->
  bv_unsigned x16 = 18446744073709551599 -> bv_unsigned x17 = 18446744073709551615 ->
  bv_unsigned x28 = 18446744073709551607 ->
  INVU m1 (3 * (ch * 12)) ->
  evt rsegs PostU (STATE 0x14028 m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
    HK Hch H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 I0.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (ch * 12 <= (nch - 1) * 12) by nia.
  pose proof (u64_range sp) as Rsp.
  apply wv in H5, H6, H7, H10, H11, H12, H13, H14, H15, H16, H17, H28.
  subst x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28.
  st. st. rewrite (land_2m2 ch) by lia. st. rewrite land1.
  eapply (up_inner ch) with (K := Z.to_nat (12 - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- INVU _ _ => eapply INVU_idx; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y9 y12 y18 y29 H8 I2. apply wv in H8. subst y8.
  st. st. st.
  brq BR.
  - st. st.
    destruct I2 as (BR2 & (junk2 & FR2) & ST2 & WA2 & MU2 & WM2 & BW2).
    eapply up_exit with (r := 12); [exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK, Hnchdef. split; [exact MU2|].
    replace (braid_out bs nch 12) with (up_pre (3 * (ch * 12 + 12))) by (unfold up_pre, braid_out; do 3 f_equal; lia).
    exact BW2.
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- INVU _ _ => eapply INVU_idx; [exact I2 | lia]
         | _ => first [ reflexivity | lia | (rewrite unsigned_lit by lia; lia) | ufin ]
         end.
Qed.

End UP.

Ltac ufail :=
  eapply up_fail; try eassumption;
  apply not_true_iff_false; rewrite up_ok_true;
  intros (U1 & U2 & U3 & U4 & U5 & U6 & U7);
  try (apply up_nch_pos in U3; destruct U3 as (V1 & V2 & V3 & V4 & V5));
  unfold inspect_byte in *; first [ lia | (Z.div_mod_to_equations; lia) ].

Theorem reac_upstream_decode_holds : reac_upstream_decode_contract.
Proof.
  unfold reac_upstream_decode_contract, REAC_UPSTREAM_DECODE, DIV36_MAGIC_AT, DIV36_MAGIC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw out lo E0 E2 Rraw Rout Rlen HMG HB HO ST LO DR DO DM.
  subst a0 a2.
  pose proof (u64_range a1) as Ra1.
  set (len := bv_unsigned a1) in *.
  assert (A1 : a1 = Z_to_bv 64 len) by (symmetry; apply Z_to_bv_bv_unsigned).
  clearbody len. subst a1.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 4 step.
  pose proof (rd_all _ _ _ HMG) as HRM. rewrite length_le8 in HRM.
  do 4 step.
  brq B1.
  { ufail. }
  step. brq B2.
  { ufail. }
  step. brq B3.
  { ufail. }
  step. step. step. step.
  replace (len + -52) with (len - 52) in * by lia.
  rewrite (unsigned_lit (len - 52)) by lia.
  step.
  rewrite (unsigned_lit (Z.shiftr _ 64)) by (rewrite Z.shiftr_div_pow2 by lia; split;
    [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]).
  rewrite div36 by lia.
  assert (QB : 2 <= (len - 52) / 36 < 2^27) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  set (q := (len - 52) / 36) in *.
  step. step. step.
  rewrite ?(unsigned_lit q) by lia. rewrite ?(unsigned_lit (q * 36)) by lia.
  rewrite ?(unsigned_lit (len - 52)) by lia.
  rewrite ?(unsigned_lit (len - 52 - q * 36)) by (subst q; Z.div_mod_to_equations; lia).
  step. brq B4.
  2:{ ufail. }
  assert (M36 : (len - 52) mod 36 = 0) by (subst q; Z.div_mod_to_equations; lia).
  step. rewrite (unsigned_lit q) by lia. step. step.
  rewrite width_test by lia.
  destruct ((2 <=? q) && (q <=? 40)) eqn:B5; cbn [negb].
  2:{ ufail. }
  apply andb_true_iff in B5. destruct B5 as [B5a B5b]. apply Z.leb_le in B5a, B5b.
  step. rewrite (unsigned_lit q) by lia. rewrite land1. step. brq B6.
  2:{ ufail. }
  assert (UQ : up_nch len = q) by (apply up_nch_val; lia).
  destruct (HB B2 B3 ltac:(lia)) as [LEN BB].
  specialize (DR B2 B3 ltac:(lia)).
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN, Z2Nat.id in BBB by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (BB1 : bytes_at rsegs mc raw bs)
      by (eapply bytes_at_transport; [exact BB | exact MU |]; cbn [disjoint_from];
          rewrite LEN, Z2Nat.id by lia; split; [lia | exact I]) end.
  clear BB. rename BB1 into BB.
  step. step. cnd false.
  pose proof (rd1 _ _ _ 12 BB ltac:(rewrite LEN; lia)) as HR. change (Z.to_nat 12) with 12%nat in HR.
  step. step. step. rewrite eqb_zxb by lia. brq B7.
  2:{ ufail. }
  clear HR.
  step. step. cnd false.
  pose proof (rd1 _ _ _ 13 BB ltac:(rewrite LEN; lia)) as HR. change (Z.to_nat 13) with 13%nat in HR.
  step. step. step. rewrite eqb_zxb by lia. brq B8.
  2:{ ufail. }
  clear HR.
  step. step. usub. rewrite ?zb_lxor_ones by lia. step. cnd false.
  pose proof (rd1 _ _ _ (len - 2) BB ltac:(rewrite LEN; lia)) as HR.
  step. step. step. step. rewrite eqb_zxb by lia. brq B9.
  2:{ ufail. }
  clear HR.
  step. step. cnd false.
  pose proof (rd1 _ _ _ (len - 1) BB ltac:(rewrite LEN; lia)) as HR.
  step. step. step. step. rewrite eqb_zxb by lia. brq B10.
  2:{ ufail. }
  clear HR.
  step. step. cnd false.
  assert (OK : up_ok raw out len bs = true).
  { rewrite up_ok_true. unfold inspect_byte. rewrite UQ. repeat split; lia. }
  destruct (HO OK) as (HW & HoutN & DOR). rewrite UQ in HW, HoutN, DOR.
  specialize (DO OK). rewrite UQ in DO.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (HW1 : wr_at rsegs mc out (36 * q)) by (eapply wr_at_transport; [exact HW | exact WM]) end.
  clear HRM HMG.
  do 12 step.
  eapply up_outer with (K := Z.to_nat (q - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
    (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11)
    (m := m) (bs := bs) (raw := raw) (out := out) (len := len) (lo := lo) (nch := q).
  all: lazymatch goal with
       | |- context [INVU] => idtac
       | |- context [UPSEP] => unfold UPSEP; split; [|split]; lia
       | _ => first [ assumption | reflexivity | lia | ufin
                    | (rewrite (unsigned_lit q) by lia; rewrite Z.add_0_r, swrap32_id by lia; apply unsigned_lit; lia) ]
       end.
  replace (3 * (0 * 12)) with 0 by lia.
  split; [exact BB|]. split; [eexists; exact FR|]. split; [exact ST|]. split; [exact HW1|].
  split; [apply munch_extend; exact MU|]. split; [exact WM|].
  unfold up_pre. change (Z.to_nat 0) with 0%nat. cbn [seq map]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
  intros i Hi. cbn [length] in Hi. lia.
Qed.
