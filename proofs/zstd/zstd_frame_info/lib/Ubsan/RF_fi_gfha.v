(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ZBridge Image Mem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_memcpy Startup_B RF_fi_iface RF_fi_small.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

(* [comment removed for export] *)
Lemma fhd_decomp : forall c, 0 <= c < 256 ->
  (Z.land c 3 = 0 \/ Z.land c 3 = 1 \/ Z.land c 3 = 2 \/ Z.land c 3 = 3)
  /\ (Z.shiftr c 6 = 0 \/ Z.shiftr c 6 = 1 \/ Z.shiftr c 6 = 2 \/ Z.shiftr c 6 = 3)
  /\ (Z.land c 32 = 0 \/ Z.land c 32 = 32) /\ (Z.land c 8 = 0 \/ Z.land c 8 = 8)
  /\ Z.land (Z.shiftr c 3) 24 = 8 * Z.shiftr c 6 /\ (c <? 64) = (Z.shiftr c 6 =? 0).
Proof.
  intros c Hc.
  pose proof (zrange_all (fun c =>
     ((Z.land c 3 =? 0) || (Z.land c 3 =? 1) || (Z.land c 3 =? 2) || (Z.land c 3 =? 3))
     && ((Z.shiftr c 6 =? 0) || (Z.shiftr c 6 =? 1) || (Z.shiftr c 6 =? 2) || (Z.shiftr c 6 =? 3))
     && ((Z.land c 32 =? 0) || (Z.land c 32 =? 32)) && ((Z.land c 8 =? 0) || (Z.land c 8 =? 8))
     && (Z.land (Z.shiftr c 3) 24 =? 8 * Z.shiftr c 6) && (Bool.eqb (c <? 64) (Z.shiftr c 6 =? 0)))%bool 256 ltac:(vm_compute; reflexivity) c Hc) as H.
  cbn beta in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.eqb_eq in H. destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6).
  apply Bool.eqb_prop in H6. split; [tauto|]. split; [tauto|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| exact H6].
Qed.

Lemma land7_mod8 : forall z, z mod 8 = 0 -> Z.land z 7 = 0.
Proof. intros z H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GFHA_FRAME : Z := 48.

(* [comment removed for export] *)
Definition gfha_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ZF n lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j1 hb j2 : list byte) (m' : fmem),
    ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(ZF, ZF + 48); (SP - GFHA_FRAME, SP)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' ZF [CB 24 j1; CB 4 hb; CB 20 j2]
    /\ stk usegs m' lo SP
    /\ (r mod 2^64 = 0 -> exists h, hb = le4 (Z_to_bv 64 h) /\ 6 <= h <= n /\ h <= 18).

(* [comment removed for export] *)
Definition gfha_stmt_at (pc : Z) (fmt : word -> Prop) : Prop :=
  forall (ra : word) (SP : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (S : Z) (bl : list Z) (ZF lo : Z) (zj : list byte),
    buf_at m S bl -> zlen bl < 2^62 ->
    rw_cells usegs m ZF [CB 48 zj] -> ZF mod 8 = 0 ->
    stk usegs m lo SP -> lo <= SP - GFHA_FRAME -> 0 <= SP < 2^64 ->
    (* [comment removed for export] *)
    (S + zlen bl <= ZF \/ ZF + 48 <= S) -> (S + zlen bl <= SP - GFHA_FRAME \/ SP <= S) ->
    (ZF + 48 <= SP - GFHA_FRAME \/ SP <= ZF) ->
    mem_inv usegs m -> fmt a3 ->
    a0 = Z_to_bv 64 ZF -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlen bl) ->
    evt usegs (gfha_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ZF (zlen bl) lo m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

Definition gfha_stmt : Prop := gfha_stmt_at PFI_GFHA (fun a3 => a3 = Z_to_bv 64 0).
Definition gfh_stmt : Prop := gfha_stmt_at PFI_GFH (fun _ => True).

(* [comment removed for export] *)
Section GFHA.
  Variables (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : fmem) (S : Z) (bl : list Z) (ZF lo : Z).
  Notation n := (zlen bl).
  Notation sp := (Z_to_bv 64 SP).
  Notation W := [(ZF, ZF + 48); (SP - GFHA_FRAME, SP)].
  Notation POST := (gfha_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ZF n lo m).
  Hypothesis BUF : buf_at m S bl.
  Hypothesis NB : n < 2^62.
  Hypothesis LO : lo <= SP - GFHA_FRAME.
  Hypothesis SPH : 0 <= SP < 2^64.
  Hypothesis SEP1 : S + n <= ZF \/ ZF + 48 <= S.
  Hypothesis SEP2 : S + n <= SP - GFHA_FRAME \/ SP <= S.
  Hypothesis SEP3 : ZF + 48 <= SP - GFHA_FRAME \/ SP <= ZF.

  (* [comment removed for export] *)
  #[using="bl LO SPH"] Lemma gfha_tail : forall nn m1 (r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (q9 q18 q19 : word)
      (j0 hb : list byte) (j1 hb4 j2 : list byte),
    (r mod 2^64 = 0 -> exists h, hb4 = le4 (Z_to_bv 64 h) /\ 6 <= h <= nn /\ h <= 18) ->
    rw_cells usegs m1 ZF [CB 24 j1; CB 4 hb4; CB 20 j2] ->
    rw_cells usegs m1 (SP + -48) [CB 4 j0; CB 4 hb; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -48) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs (gfha_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ZF nn lo m)
      (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 (Z_to_bv 64 r) q9 x10 x11 x12 x13 x14 x15 x16 x17 q18 q19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x12e7c) fc None m1 (seg_rom usegs)).
  Proof.
    intros until j2. intros RH CZ FR ST MU WM MI. unfold GFHA_FRAME in *.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
    Local Ltac2 Set LiaHints.tbl := fun () => "0070>13765370225.7316014780785.7418931827057.7227481399921.7342303277385.646372778097.73 7870555558.65 00000Q01201S02402<02]02hS3BUF2NB2LO3SPH4SEP14SEP24SEP32FBS3BUF2NB2LO3SPH4SEP14SEP24SEP32FBS3BUF2NB2LO3SPH4SEP14SEP24SEP32FBS3BUF2NB2LO3SPH4SEP14SEP24SEP32FBS3SPH2FBS3BUF2NB2LO3SPH4SEP14SEP24SEP32FBS2LO3SPH2FB".
do 7 zstep.
    release_frame FR ST SP.
    zstep. finish. all: try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. all: try lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition main_at (m0 : fmem) (j0 hb zj : list byte) (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 q19 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 (Z_to_bv 64 5) s1 (Z_to_bv 64 ZF) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 0)
             x14 x15 x16 x17 s2 q19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x12f04) fc None m0 (seg_rom usegs).
  Definition main_ok : Prop := forall m0 j0 hb zj x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 q19,
    5 <= n -> 0 < S ->
    rw_cells usegs m0 ZF [CB 48 zj] ->
    rw_cells usegs m0 (SP + -48) [CB 4 j0; CB 4 hb; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs m0 S (map (Z_to_bv 8) bl) ->
    stk usegs m0 lo (SP + -48) -> munch W m m0 -> wmono usegs m m0 -> mem_inv usegs m0 ->
    evt usegs POST (main_at m0 j0 hb zj x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 q19).

  (* [comment removed for export] *)
  Ltac hbuf_call k FR PL LJ0 :=
    lazymatch type of FR with
    | rw_cells _ ?m1 ?A (CB 4 ?j0 :: C4 ?w :: ?rest) =>
        (* [comment removed for export] *)
        apply (rw_cells_reshape m1 A _ (CB 4 j0 :: CB k (firstn k (le4 w)) :: CB (4 - k) (skipn k (le4 w)) :: rest)) in FR;
          [| cbn [cells_wf cell_wf]; rewrite ?length_firstn, ?length_skipn, ?length_le4; repeat split; first [exact LJ0 | reflexivity | lia]
           | cbn [cells_bytes cbytes]; rewrite <- (firstn_skipn k (le4 w)) at 3; rewrite <- ?app_assoc; reflexivity
           | reflexivity ];
        let FRa := fresh "FRa" in let FRb := fresh "FRb" in let FRc := fresh "FRc" in
        apply (proj1 (rw_cells_app m1 A [CB 4 j0] _)) in FR; destruct FR as [FRa FRb]; cbn [cells_size csize Nat.add] in FRb;
        apply (proj1 (rw_cells_app m1 _ [CB k (firstn k (le4 w))] _)) in FRb; destruct FRb as [FRb FRc]; cbn [cells_size csize Nat.add] in FRc;
        replace (A + Z.of_nat 4) with (SP + -44) in FRb, FRc by lia;
        (* [comment removed for export] *)
        zstep;
        lazymatch type of PL with bytes_at _ _ ?S _ =>
          call (rmemcpy_specZ (SP + -44) S (Z.of_nat k));
            [exact PL | rewrite length_map, Nat2Z.id; lia | rewrite Nat2Z.id; exact FRb | lia | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia |]
        end;
        (* [comment removed for export] *)
        lazymatch goal with
        | PC : rw_cells _ ?m2 _ [CB _ ?src] |- _ =>
          rewrite Nat2Z.id in PC;
          let FRbc := fresh "FRbc" in
          assert (FRbc : rw_cells usegs m2 (SP + -44) ([CB k src] ++ (CB (4 - k) (skipn k (le4 w)) :: rest)))
            by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact PC| cbn [cells_size csize Nat.add];
                 match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -44 + Z.of_nat k) by lia end; exact FRc]);
          clear PC FRc;
          apply (rw_cells_merge usegs m2 (SP + -44) [] [CB k src; CB (4 - k) (skipn k (le4 w))] rest) in FRbc; cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRbc;
          assert (FR : rw_cells usegs m2 A ([CB 4 j0] ++ (CB 4 (src ++ skipn k (le4 w)) :: rest)))
            by (apply (proj2 (rw_cells_app m2 _ _ _)); split; [exact FRa| cbn [cells_size csize Nat.add];
                 match goal with |- rw_cells _ _ ?a _ => replace a with (SP + -44) by lia end;
                 lazymatch type of FRbc with rw_cells _ _ _ [CB _ ?bb; _] => idtac | _ => idtac end; first [exact FRbc | rewrite <- app_assoc in FRbc; exact FRbc]]);
          clear FRa FRbc; cbn [app] in FR
        end
    end.

  (* [comment removed for export] *)
  Ltac small_tail := eapply gfha_tail; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; (let HR := fresh in intros HR; exfalso; vm_compute in HR; lia).
  Ltac hbuf_call_find k :=
    lazymatch goal with
    | FRx : rw_cells _ _ (SP + -48) (CB 4 _ :: C4 _ :: _), PLx : bytes_at _ _ S _, LJx : length _ = 4%nat |- _ =>
        hbuf_call k FRx PLx LJx
    end.
  Ltac small_path k :=
    hbuf_call_find k; try rename MI0 into MI;
    zstep; zstep; let KQ := fresh "KQ" in if_cases KQ; zify_cond KQ;
    [ small_tail
    | do 6 zstep; hbuf_call_find k; try rename MI0 into MI;
      do 5 zstep; let KQ2 := fresh "KQ" in if_cases KQ2; zify_cond KQ2; [ small_tail | do 3 zstep; small_tail ] ].

  (* [comment removed for export] *)
  Definition zcell := Z_to_bv 64 0.
  Definition dec_at (m1 : fmem) (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 q19 : word) : machine_state :=
    MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 (Z_to_bv 64 5) s1 (Z_to_bv 64 ZF) (Z_to_bv 64 S) (Z_to_bv 64 n) (Z_to_bv 64 (Znth 4 bl))
             x14 x15 x16 x17 s2 q19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
       F (Z_to_bv 64 0x12fbc) fc None m1 (seg_rom usegs).
  Definition dec_ok (D : Z) : Prop := forall m1 j0 hb x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 q19,
    5 <= n -> Z.land (Znth 4 bl) 3 = D ->
    rw_cells usegs m1 ZF [C8 zcell; C8 zcell; C4 zcell; C4 zcell; C4 zcell; C4 zcell; C4 zcell; C4 zcell; C8 zcell] ->
    rw_cells usegs m1 (SP + -48) [CB 4 j0; CB 4 hb; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at usegs m1 S (map (Z_to_bv 8) bl) ->
    stk usegs m1 lo (SP + -48) -> munch W m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (dec_at m1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 q19).

  #[using="BUF NB LO SPH SEP1 SEP2 SEP3"] Lemma gfha_entry : main_ok -> forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (zj : list byte),
    rw_cells usegs m ZF [CB 48 zj] -> stk usegs m lo SP -> mem_inv usegs m -> a3 = Z_to_bv 64 0 ->
    evt usegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ZF) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFI_GFHA) fc None m (seg_rom usegs)).
  Proof.
    intros MAIN. unfold main_ok, main_at in MAIN. intros until zj. intros CZ ST MI ->. unfold PFI_GFHA, GFHA_FRAME in *.
    destruct BUF as [PL PLR]. pose proof (bytes_at_bound _ _ _ _ PL) as BB. rewrite length_map in BB.
    assert (LENB : Z.of_nat (length (map (Z_to_bv 8) bl)) = n) by (rewrite length_map; reflexivity).
    pose proof (rw_cells_bound _ _ _ _ CZ) as ZB. cbn [cells_size csize Nat.add] in ZB.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM. unfold GFHA_FRAME in MU.
    assert (ST0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    Local Ltac2 Set LiaHints.tbl := fun () => "01Y0?11799489569.10111799489569.10211801586693.85 11801586693.86 13113690578.69 13315475890.98 13765370225.69 13959648727.68 1414253356.68  16014780785.69 16073487306.65 16075583565.63 16075583565.64 16075584458.63 16075584458.64 16297174487.68 16314762450.66 16757939346.10216760036534.86 18612176510.66 18898871378.68 18931827057.66 20059885906.68 20727986540.75 20727986540.92 22700267513.10322700267513.87 24938982063.64 2663801715.86  2665898839.102 27481399921.68 28001097132.66 29181089099.83 29183236896.67 32245710039.66 33680001082.69 34009807404.68 34466804606.69 39304366957.54 39708328663.75 39708328663.92 40202209158.56 40428100743.66 40428100743.68 40428100743.69 40428100743.75 40428100743.92 40823198830.97 42078159536.67 42080210139.83 42090697947.81 42090697947.97 42799229438.68 44484923210.85 44487020398.10145221239098.69 45445178071.69 52069598124.69 52191540352.67 52193622763.83 52230632470.82 53415683838.68 563227834.68   56372266706.69 57745675194.68 59308628820.64 59310725331.65 59314873579.64 59314873579.65 59314873579.66 59314873579.82 59314873579.98 60151666007.83 60153748284.67 60385159294.69 60566025431.69 6057945287.83  6059992748.67  61322431053.83 61324575782.67 62539661169.10262539661169.75 62539661169.81 62539661169.86 62539661169.92 62539661169.97 6372778097.68  63970649013.57 64026414714.75 64026414714.92 64106014380.69 64302930659.62 64738246334.75 64738246334.92 66611618194.75 66611618194.92 67748373186.98 67750470374.82 8326742054.83  8328891981.67  8461548835.83  8463594312.67  8583720762.66  881000923.85   883098111.101  00000?00N00]00l01@01O02C03703I04=04O04a05305E05W06K06_07B07e08H08\09P09d0:60:H0;e0=>0=S0=T0=U0>I0>[0>j0?90?m0@?0@Q0A40A?0B90C60C>0CM0C\0Ck0D:0DI0DX0Dg0E60EE0ET0F70FF0FU0Fg0G[0Gm0HA0HU0Hd0IG0IY0Im0J?0JT0Jj0K;0KL0K]0Kn0L?0LQ0Lc0MF0N:0N[0O<0O]0P>0Q;0R50S20So0Tl0Ui0V]0W<0WN0W`0X20X30XV0Y90YM0Ya0Z00Z?0Z`0[A0[P0[_0\10\E0\YS3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S2NB3SPH2ZB2LJ3LJ0S2NB3SPH2ZB2LJ3LJ0S2NB3SPH2ZB2LJ3LJ0S2NB3SPH2ZB2LJ3LJ0S2NB3SPH2ZB2LJ3LJ0S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH2ZB2LJ3LJ02HBS3BUF2NB2LO3SPH4SEP14SEP24SEP34MAIN3PLR2BB4LENB2ZB2WM3ST02LJ3LJ02KF2KS2K52K02EN2MI2KQ5POST01HS3BUF2NB2LO3SPH4SEP14SEP24SEP34MAIN2MI3PLR2BB4LENB2ZB2WM3ST02LJ3LJ02KF2KS2K52K02EN4POST1HS3SPH2ZB2LJ3LJ02K52K0FFS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH2ZB2LJ3LJ02HBS3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S2LO3SPH2ZBS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K5S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K52ENS3SPH2ZBS3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH4SEP22ZB2LJ3LJ0S3SPH4SEP22ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH4SEP32ZB2LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH2ZB2LJ3LJ02K02K5S3SPH2ZB2LJ3LJ02K03K00S3SPH2ZB2LJ3LJ01HS3SPH2ZB2LJ3LJ01HS3SPH2ZB2LJ3LJ01HS3SPH2ZB2LJ3LJ01HS3SPH2ZB2LJ3LJ01HS3SPH2BB2ZB2LJ3LJ0S3SPH2BB2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH4SEP14SEP24SEP32ZB2LJ3LJ02ENS3SPH4SEP14SEP24SEP32ZB2LJ3LJ02ENS3SPH4SEP14SEP24SEP32ZB2LJ3LJ02ENS3SPH4SEP14SEP24SEP32ZB2LJ3LJ02ENS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K52ENS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K5S3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K52ENS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K52ENS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K52ENS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ02KF2K52ENS3BUF2NB2LO3SPH4SEP14SEP24SEP32BB4LENB2ZB3ST02LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJS3SPH2ZB2LJ3LJ02HBS3SPH2ZB2LJ3LJ02HBS3SPH2ZB2LJ3LJ02HBFS3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP34LENB2ZB2LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH4SEP14SEP24SEP32ZB2LJ3LJ02ENS3SPH4SEP14SEP24SEP32ZB2LJ3LJ02ENS3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ0S3SPH2ZB2LJ3LJ02HBS3SPH4SEP32ZB2LJ3LJ0S3SPH4SEP32ZB2LJ3LJ0".
carve_frame 48%nat ST.
    (* [comment removed for export] *)
    assert (LJ : length junk = 48%nat) by exact (proj1 (proj1 (proj1 FR))).
    apply (rw_cells_split_CB usegs m _ [] 48 junk [] [4; 4; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    set (j0 := firstn 4 junk) in FR. assert (LJ0 : length j0 = 4%nat) by (subst j0; rewrite length_firstn; lia). clearbody j0.
    do 6 zstep.                                  (* [comment removed for export] *)
    zstep. if_cases KF; zify_cond KF. 2:{ exfalso. apply KF. reflexivity. }
    zstep.                                       (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      zstep. if_cases K5; zify_cond K5.
      + (* [comment removed for export] *) eapply MAIN; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; lia.
      + zstep. if_cases K0; zify_cond K0.
        * (* [comment removed for export] *)
          apply (rw_cells_split_CB usegs _ _ [] 48 zj [] [24; 4; 20]%nat) in CZ; [| reflexivity]. cbn [app mk_CB_cells] in CZ.
          small_tail.
        * (* [comment removed for export] *)
          zstep. zstep. if_false. zstep. zstep.  (* [comment removed for export] *)
          zstep. (* [comment removed for export] *) zstep. zstep. zstep. (* [comment removed for export] *)
          apply (rw_cells_split_CB usegs _ _ [] 48 zj [] [24; 4; 20]%nat) in CZ; [| reflexivity]. cbn [app mk_CB_cells] in CZ.
          (* [comment removed for export] *)
          assert (EN : n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
          destruct EN as [EN|[EN|[EN|EN]]]; rewrite EN in *.
          -- small_path 1%nat. -- small_path 2%nat. -- small_path 3%nat. -- small_path 4%nat.
    - (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *) zstep. if_cases K5; zify_cond K5; [exfalso; lia|]. zstep. if_cases K00; zify_cond K00; [| exfalso; lia].
        apply (rw_cells_split_CB usegs _ _ [] 48 zj [] [24; 4; 20]%nat) in CZ; [| reflexivity]. cbn [app mk_CB_cells] in CZ.
        small_tail.
      + (* [comment removed for export] *) zstep.
        apply (rw_cells_split_CB usegs _ _ [] 48 zj [] [24; 4; 20]%nat) in CZ; [| reflexivity]. cbn [app mk_CB_cells] in CZ.
        small_tail.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Ltac zf_generic :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF ?cs |- _ =>
        let j := fresh "zj" in let C := fresh "CZ" in
        destruct (rw_cells_forget usegs m1 ZF cs CZ) as [j C]; clear CZ; cbn [cells_size csize Nat.add] in C;
        apply (rw_cells_split_CB usegs _ _ [] 48 j [] [24; 4; 20]%nat) in C; [| reflexivity]; cbn [app mk_CB_cells] in C
    end.
  Ltac exit_tail := zf_generic; small_tail.
  (* [comment removed for export] *)
  Ltac zf_success :=
    lazymatch goal with
    | CZ : rw_cells _ ?m1 ZF [?c0; ?c1; ?c2; ?c3; C4 ?h; ?c5; ?c6; ?c7; ?c8] |- _ =>
        apply (rw_cells_reshape m1 ZF _ [CB 24 (cbytes c0 ++ cbytes c1 ++ cbytes c2 ++ cbytes c3); CB 4 (le4 h);
                                       CB 20 (cbytes c5 ++ cbytes c6 ++ cbytes c7 ++ cbytes c8)]) in CZ;
        [| cbn [cells_wf cell_wf cbytes]; rewrite ?app_length, ?length_le8, ?length_le4; repeat split; reflexivity
         | cbn [cells_bytes cbytes]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity
         | reflexivity ]
    end;
    eapply gfha_tail; try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; intros _; eexists; split; [reflexivity| lia].
  (* [comment removed for export] *)
  Ltac brr := first [if_true | if_false].

  (* [comment removed for export] *)
  Ltac pose_rds2 a b :=
    let t := eval vm_compute in (Z.ltb a b) in
    lazymatch t with
    | true => pose_rd a; let a' := eval vm_compute in (a + 1) in pose_rds2 a' b
    | false => idtac
    end.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fhtab_read_at : forall m1 k A, mem_inv usegs m1 -> 0 <= k < 8 -> A = PFI_DIDTAB + 8 * k ->
    ov_read_bytes usegs m1 (wa A) 8 = Some (map (Z_to_bv 8) (firstn 8 (skipn (Z.to_nat (8 * k)) FHTAB))).
  Proof. intros m1 k A MI1 Hk ->. apply fhtab_read; assumption. Qed.
  Ltac pose_tab k :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MIx : mem_inv usegs m1 |- _ =>
        let A := eval vm_compute in (PFI_DIDTAB + 8 * k) in
        let H := fresh "TAB" in
        pose proof (fhtab_read_at m1 k A MIx ltac:(lia) ltac:(reflexivity)) as H;
        lazymatch type of H with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in H end
      end
    end.

  (* [comment removed for export] *)
  Ltac gstep L Hd Hs Hr Hf E24 E64 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 77380 => first [ zf_success | exit_tail ]                                   (* [comment removed for export] *)
      | 77704 => zstep; let K := fresh "KL" in if_cases K; zify_cond K;            (* [comment removed for export] *)
                 [ zstep; clear_rd; pose_rds2 4 L | ]
      | 77724 => zstep; cbv beta; lazymatch goal with RB : 0 <= Znth 4 bl < 256 |- _ => rewrite (byte_lit _ RB) end   (* [comment removed for export] *)
      | 77732 => zstep; let K := fresh "KR" in if_cases K; zify_cond K          (* [comment removed for export] *)
      | 77744 => zstep; cbv beta; lazymatch goal with RB : 0 <= Znth 5 bl < 256 |- _ => rewrite (byte_lit _ RB) end   (* [comment removed for export] *)
      | 77752 => zstep; let K := fresh "KW" in if_cases K; zify_cond K          (* [comment removed for export] *)
      | 78244 => zstep; let K := fresh "KB" in if_cases K; clear K               (* [comment removed for export] *)
      | _ => zstep; rewrite ?Hd, ?Hs, ?Hr, ?E24, ?E64, ?Hf; try brr
      end
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 1 "gstep: undecided branch at" pc
    end.

End GFHA.
