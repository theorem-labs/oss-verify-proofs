(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): satisfiability witnesses of the function-specific
   premises of LinkVfDefs.v's two contracts, each at the state of a real call, as closed lemmas:
   - F2, reac_served_mark 0x89aec (`fprintf (g_say, .str.8, name)`, a2 = name) on the first mark after the rewind:
     the FILE as fmemopen and rewind leave it (k = 0, flags F_NORD, orientation 0, window empty, pos = len = 0), the
     name "eth0", the format .str.8 0x21500 as the image holds it;
   - V1, reac_code_emit 0x89d1c (`vfprintf (f, .str.5, ap)`), right after F1 0x89d00 printed "reac-pw: E_NOT_MARKED "
     on that FILE: 22 bytes pending, the window active, orientation -1 (F1's __towrite), the four slots at ap =
     reac_code_emit's spill of a4..a7 (entry sp - 0x20): name, .str.4 "reac-pw:served", -ret = 1 (ret = -1),
     .str.6 ": this daemon has no CAP_NET_ADMIN" (reac_served_mark 0x89b7c..0x89b9c).
   The memory: the image's bytes (the formats, the .got cell 0xa2658), the FILE block at a heap address WF as
   AMemFile.v's amf_state writes it, the name in a heap block WN, the guard word, the slots, and the shadow: every
   granule of the live objects addressable (0, or the count of its live bytes), every other shadow byte 0xf9. The
   hidden map is empty. The family is pf_family pf_link_piece (lib/Rt/SnShared.v), the core of the top lemmas'
   family; the AR state and the journal of the callers are not here (no AR state of image A is on this branch; the
   whole pre is written out in the final report). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YA0n YP09 YP02 YI04 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkPfPiece.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. Checkers (a boolean over a finite range, and what it gives)
   ========================================================================== *)

Definition bytes_okb (rd : reader) (a : Z) (l : list Z) : bool :=
  forallb (fun k => match rd (a + Z.of_nat k) with Some v => v =? nth k l 0 | None => false end) (seq 0 (length l)).

Lemma bytes_okb_sound : forall rd a l, bytes_okb rd a l = true ->
  forall i, 0 <= i < Z.of_nat (length l) -> rd (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
  intros rd a l H i Hi. unfold bytes_okb in H. rewrite forallb_forall in H.
  assert (Hin : In (Z.to_nat i) (seq 0 (length l))) by (apply in_seq; lia).
  specialize (H _ Hin). rewrite Z2Nat.id in H by lia.
  destruct (rd (a + i)) as [v|]; [|discriminate]. apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Definition some_okb (rd : reader) (lo hi : Z) : bool :=
  forallb (fun k => match rd (lo + Z.of_nat k) with Some _ => true | None => false end) (seq 0 (Z.to_nat (hi - lo))).

Lemma some_okb_sound : forall rd lo hi, some_okb rd lo hi = true -> forall x, lo <= x < hi -> rd x <> None.
Proof.
  intros rd lo hi H x Hx. unfold some_okb in H. rewrite forallb_forall in H.
  assert (Hin : In (Z.to_nat (x - lo)) (seq 0 (Z.to_nat (hi - lo)))) by (apply in_seq; lia).
  specialize (H _ Hin). replace (lo + Z.of_nat (Z.to_nat (x - lo))) with x in H by lia.
  destruct (rd x); [discriminate | discriminate H].
Qed.

Definition shadow_okb (rd : reader) (x n : Z) : bool :=
  forallb (fun k => let a := x + Z.of_nat k in
    match rd (shadow_of_addr SHADOW_OFF a) with
    | Some s => (s =? 0) || ((a mod 8 <? s) && (s <? 8))
    | None => false
    end) (seq 0 (Z.to_nat n)).

Lemma shadow_okb_sound : forall rd x n, shadow_okb rd x n = true -> range_addressable rd SHADOW_OFF x n.
Proof.
  intros rd x n H y Hy. unfold shadow_okb in H. rewrite forallb_forall in H.
  assert (Hin : In (Z.to_nat (y - x)) (seq 0 (Z.to_nat n))) by (apply in_seq; lia).
  specialize (H _ Hin). cbv zeta in H. replace (x + Z.of_nat (Z.to_nat (y - x))) with y in H by lia.
  destruct (rd (shadow_of_addr SHADOW_OFF y)) as [s|]; [|discriminate]. exists s. split; [reflexivity|].
  unfold saddr_ok. apply orb_true_iff in H as [H | H].
  - left. apply Z.eqb_eq. exact H.
  - right. apply andb_true_iff in H as [H1 H2]. apply Z.ltb_lt in H1, H2. lia.
Qed.

Lemma hull_okb_sound : forall rd x n,
  some_okb rd (shadow_addr x / 8 * 8) (shadow_addr (x + n - 1) / 8 * 8 + 8) = true -> shadow_hull_vis rd x n.
Proof. intros rd x n H s Hs. exact (some_okb_sound _ _ _ H s Hs). Qed.

Definition words_okb (rd : reader) (p : Z) (ws : list Z) : bool :=
  forallb (fun k => match rdword rd (p + 8 * Z.of_nat k) with Some v => v =? nth k ws 0 | None => false end)
    (seq 0 (length ws)).

Lemma words_okb_sound : forall rd p ws, words_okb rd p ws = true -> words_at rd p ws.
Proof.
  intros rd p ws H i Hi. unfold words_okb in H. rewrite forallb_forall in H.
  assert (Hin : In i (seq 0 (length ws))) by (apply in_seq; lia).
  specialize (H _ Hin). destruct (rdword rd (p + 8 * Z.of_nat i)) as [v|]; [|discriminate].
  apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Definition zbytes_okb (m : word -> option byte) (a : Z) (l : list Z) : bool :=
  forallb (fun k => match amf_rd tfibsegs m (a + Z.of_nat k) with Some v => v =? nth k l 0 | None => false end)
    (seq 0 (length l)).

Lemma zbytes_okb_sound : forall m a l, zbytes_okb m a l = true -> azbytes tfibsegs m a l.
Proof.
  intros m a l H i Hi. unfold zbytes_okb in H. rewrite forallb_forall in H.
  assert (Hin : In i (seq 0 (length l))) by (apply in_seq; lia).
  specialize (H _ Hin). destruct (amf_rd tfibsegs m (a + Z.of_nat i)) as [v|]; [|discriminate].
  apply Z.eqb_eq in H. subst. reflexivity.
Qed.

(* ==========================================================================
   2. The state
   ========================================================================== *)

Definition WF : Z := 0x606000000020.   (* the FILE block: fmemopen's 1304-byte chunk of the allocator's heap *)
Definition WN : Z := 0x602000000010.   (* the interface name "eth0", a heap block *)
Definition WSP : Z := 0x7ffffffde000.  (* sp at the call *)
Definition WAP : Z := WSP + 0x60.      (* V1: ap = reac_code_emit's entry sp - 0x20, its sp being entry - 0x80 *)
Definition WCANARY : Z := 0x2f3a5e6b7c8d9e01.

Definition w_name : list Z := [101; 116; 104; 48].                       (* "eth0" *)
Definition STR4 : Z := 0x213c0.  (* "reac-pw:served" *)
Definition STR5 : Z := 0x213e0.  (* V1's format *)
Definition STR6 : Z := 0x21480.  (* ": this daemon has no CAP_NET_ADMIN" *)
Definition STR8 : Z := 0x21500.  (* F2's format *)
Definition w_slots : list Z := [WN; STR4; 1; STR6].                     (* V1's four slots *)

(* the formats and strings as the image holds them (the pin's .rodata, read with pyelftools) *)
Definition fmt8 : list Z := [114; 101; 97; 99; 45; 112; 119; 58; 32; 91; 37; 115; 93; 32; 105; 115; 32; 97; 32; 86;
  76; 65; 78; 32; 116; 104; 101; 32; 104; 111; 115; 116; 32; 109; 97; 100; 101; 32; 226; 128; 148; 32; 110; 111; 116;
  32; 109; 97; 114; 107; 101; 100; 59; 32; 105; 102; 32; 97; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110;
  97; 103; 101; 114; 32; 99; 111; 110; 102; 105; 103; 117; 114; 101; 115; 32; 105; 116; 44; 32; 103; 105; 118; 101;
  32; 105; 116; 32; 110; 111; 32; 97; 100; 100; 114; 101; 115; 115; 101; 115; 32; 116; 104; 101; 114; 101; 10].
Definition fmt5 : list Z := [91; 37; 115; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 109; 97; 114; 107;
  32; 105; 116; 32; 39; 37; 115; 39; 32; 40; 101; 114; 114; 110; 111; 32; 37; 100; 41; 37; 115; 32; 226; 128; 148; 32;
  116; 104; 101; 32; 104; 111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97; 103;
  101; 114; 32; 105; 115; 32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111; 32; 108; 101; 97; 118; 101; 32;
  105; 116; 32; 97; 108; 111; 110; 101; 10].
Definition str4 : list Z := [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100].
Definition str6 : list Z := [58; 32; 116; 104; 105; 115; 32; 100; 97; 101; 109; 111; 110; 32; 104; 97; 115; 32; 110;
  111; 32; 67; 65; 80; 95; 78; 69; 84; 95; 65; 68; 77; 73; 78].

(* the texts *)
Definition T_F1 : list Z := [114; 101; 97; 99; 45; 112; 119; 58; 32; 69; 95; 78; 79; 84; 95; 77; 65; 82; 75; 69;
  68; 32].
Definition T_F2 : list Z := [114; 101; 97; 99; 45; 112; 119; 58; 32; 91; 101; 116; 104; 48; 93; 32; 105; 115; 32; 97;
  32; 86; 76; 65; 78; 32; 116; 104; 101; 32; 104; 111; 115; 116; 32; 109; 97; 100; 101; 32; 226; 128; 148; 32; 110;
  111; 116; 32; 109; 97; 114; 107; 101; 100; 59; 32; 105; 102; 32; 97; 32; 110; 101; 116; 119; 111; 114; 107; 32;
  109; 97; 110; 97; 103; 101; 114; 32; 99; 111; 110; 102; 105; 103; 117; 114; 101; 115; 32; 105; 116; 44; 32; 103;
  105; 118; 101; 32; 105; 116; 32; 110; 111; 32; 97; 100; 100; 114; 101; 115; 115; 101; 115; 32; 116; 104; 101; 114;
  101; 10].
Definition T_V1 : list Z := [91; 101; 116; 104; 48; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 109; 97;
  114; 107; 32; 105; 116; 32; 39; 114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 39; 32; 40; 101;
  114; 114; 110; 111; 32; 49; 41; 58; 32; 116; 104; 105; 115; 32; 100; 97; 101; 109; 111; 110; 32; 104; 97; 115; 32;
  110; 111; 32; 67; 65; 80; 95; 78; 69; 84; 95; 65; 68; 77; 73; 78; 32; 226; 128; 148; 32; 116; 104; 101; 32; 104;
  111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97; 103; 101; 114; 32; 105; 115;
  32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111; 32; 108; 101; 97; 118; 101; 32; 105; 116; 32; 97; 108;
  111; 110; 101; 10].

(* the live objects whose granules are addressable: (start, size with the NUL) *)
Definition w_live : list (Z * Z) :=
  [(STR8, 118); (STR5, 103); (STR4, 15); (STR6, 35); (WN, 5)].

(* the shadow byte of the granule at g *)
Definition w_sh (g : Z) : Z :=
  fold_right (fun r acc =>
    if (fst r <=? g) && (g + 8 <=? fst r + snd r) then 0
    else if (fst r <=? g) && (g <? fst r + snd r) then fst r + snd r - g else acc) 0xf9 w_live.

(* the memory under the FILE's stores; b: F1's 22 bytes are pending in the buffer (V1) *)
Definition w_base (b : bool) (a : word) : option byte :=
  let z := bv_unsigned a in
  if (kLowShadowBeg <=? z) && (z <? kHighShadowEnd) then Some (Z_to_bv 8 (w_sh ((z - SHADOW_OFF) * 8)))
  else if (WN <=? z) && (z <? WN + 8) then Some (Z_to_bv 8 (nth (Z.to_nat (z - WN)) (w_name ++ [0; 0; 0; 0]) 0))
  else if (WAP <=? z) && (z <? WAP + 32) then
    Some (Z_to_bv 8 (YO0f.le_byte (nth (Z.to_nat ((z - WAP) / 8)) w_slots 0) 8 (Z.to_nat ((z - WAP) mod 8))))
  else if (LA_GUARD <=? z) && (z <? LA_GUARD + 8) then Some (Z_to_bv 8 (YO0f.le_byte WCANARY 8 (Z.to_nat (z - LA_GUARD))))
  else if b && (WF + AMF_BUF <=? z) && (z <? WF + AMF_BUF + 22) then Some (Z_to_bv 8 (nth (Z.to_nat (z - WF - AMF_BUF)) T_F1 0))
  else None.

(* F2: the FILE as fmemopen and the first rewind leave it *)
Definition w_mem_F2 : word -> option byte := amf_state link_amf (w_base false) WF AF_NORD 0 0 0 0 0 0.
(* V1: after F1 (__towrite ran: orientation -1, the window active, 22 bytes pending) *)
Definition w_mem_V1 : word -> option byte :=
  amf_state link_amf (w_base true) WF AF_NORD AU32M1 (WF + AMF_BUF + AMF_BUFSIZ) (WF + AMF_BUF + 22) (WF + AMF_BUF) 0 0.

Definition wH0 : word -> bool := fun _ => false.

(* ==========================================================================
   3. The FILE premises
   ========================================================================== *)

(* a closed order fact, by computation *)
Ltac zc := first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity ].

Lemma w_bounds : 0 < WF /\ WF + AMF_BLOCK <= 2 ^ 64.
Proof. unfold WF, AMF_BLOCK. lia. Qed.

Lemma w_place : amf_place link_amf WF.
Proof.
  cbv [amf_place amf_apart amf_ofl_head link_amf amf_sink_addr amf_say_addr amf_threaded amf_need_locks amf_ofl_lock
    WF AMF_BLOCK]. lia.
Qed.

Lemma w_fld : forall M fl om wend wpos wbase pos len off n v, 0 <= off -> off + Z.of_nat n <= AMF_ZEROED ->
  val_mem tfibsegs (amf_dynw (amf_fm link_amf M WF) WF fl om wend wpos wbase pos len) (WF + off) n v ->
  val_mem tfibsegs (amf_state link_amf M WF fl om wend wpos wbase pos len) (WF + off) n v.
Proof.
  intros M fl om wend wpos wbase pos len off n v H0 H1 H. unfold amf_state.
  eapply amf_val_mem_frame; [|exact H]. intros x Hx. apply (amf_heads_set_file tfibsegs link_amf); [exact w_place | lia].
Qed.

(* a field of the FILE as amf_state writes it (AMemFile.v's amf_ar / amf_fld, which are local to its section) *)
Ltac w_ar := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AMF_COOKIE, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia.
Ltac w_amf_fld :=
  repeat first
    [ apply amf_val_mem_upd_same; w_ar
    | apply amf_val_mem_upd_zero; w_ar
    | apply amf_val_mem_upd_other; [w_ar | w_ar | w_ar | ] ].
Ltac w_fldt := apply w_fld; [try unfold AMF_COOKIE; lia
  | try unfold AMF_ZEROED; try unfold AMF_COOKIE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
  | unfold amf_dynw, amf_fm; pose proof w_bounds as [? ?]; w_amf_fld].

Lemma w_file_F2 :
  amf_k tfibsegs link_amf (mrestrict wH0 w_mem_F2) WF 0 /\
  amf_dyn tfibsegs link_amf (mrestrict wH0 w_mem_F2) WF AF_NORD 0 0 0 0 0 0 /\
  amf_pend tfibsegs (mrestrict wH0 w_mem_F2) WF [] /\ Z.of_nat (length (@nil Z)) = 0.
Proof.
  change (mrestrict wH0 w_mem_F2) with w_mem_F2. unfold w_mem_F2.
  split; [split|split; [|split; [intros i Hi; cbn in Hi; lia | reflexivity]]].
  - apply (amf_state_at tfibsegs link_amf); [exact w_place | zc | left; reflexivity | left; reflexivity
      | left; repeat split | lia | zc].
  - left. split; [reflexivity|]. split; [w_fldt|]. split; w_fldt.
  - unfold amf_dyn. repeat split; try zc; w_fldt.
Qed.

Lemma w_file_V1 :
  amf_k tfibsegs link_amf (mrestrict wH0 w_mem_V1) WF 22 /\
  amf_dyn tfibsegs link_amf (mrestrict wH0 w_mem_V1) WF AF_NORD AU32M1
    (WF + AMF_BUF + AMF_BUFSIZ) (WF + AMF_BUF + 22) (WF + AMF_BUF) 0 0 /\
  amf_pend tfibsegs (mrestrict wH0 w_mem_V1) WF T_F1 /\ Z.of_nat (length T_F1) = 22.
Proof.
  split; [|split; [|split; [unfold amf_pend; apply zbytes_okb_sound; vm_compute; reflexivity | reflexivity]]].
  - change (mrestrict wH0 w_mem_V1) with w_mem_V1. unfold w_mem_V1. split.
    + apply (amf_state_at tfibsegs link_amf); [exact w_place | zc | left; reflexivity | right; reflexivity
        | right; exists 22; unfold AMF_BUFSIZ; repeat split; lia | lia | zc].
    + right. split; [unfold AMF_BUFSIZ; lia|]. split; [w_fldt|]. split; w_fldt.
  - change (mrestrict wH0 w_mem_V1) with w_mem_V1. unfold w_mem_V1.
    unfold amf_dyn. repeat split; try zc; w_fldt.
Qed.

(* ==========================================================================
   4. The call's other function-specific premises
   ========================================================================== *)

Definition w_rd (M : word -> option byte) : reader := aview tfibsegs wH0 M.

Lemma len_app1 : forall l : list Z, Z.of_nat (length (l ++ [0])) = Z.of_nat (length l) + 1.
Proof. intros l. rewrite length_app, Nat2Z.inj_add. reflexivity. Qed.
Lemma len_fmt8 : Z.of_nat (length fmt8) = 117. Proof. reflexivity. Qed.
Lemma len_fmt5 : Z.of_nat (length fmt5) = 102. Proof. reflexivity. Qed.
Lemma len_name : Z.of_nat (length w_name) = 4. Proof. reflexivity. Qed.
Lemma len_slots : Z.of_nat (length w_slots) = 4. Proof. reflexivity. Qed.

(* the disjointness of two concrete ranges *)
Ltac w_zd := cbv [zdisjoint vmf_out LFP_STK LVF_STK LVF_MUSL_STK WF WN WSP WAP AMF_BLOCK STR4 STR5 STR6 STR8
  LA_GOT_GUARD LA_GUARD fst snd]; rewrite ?len_fmt8, ?len_fmt5, ?len_slots; lia.
(* Forall over a concrete list of ranges *)
Ltac w_fa := try unfold vmf_out; repeat (first [apply Forall_nil | apply Forall_cons]).

Lemma w_string : forall M K rs s w, rs = vmf_out K WSP WF -> 0 <= K <= 8192 ->
  Forall (fun c => 0 < c < 256) s -> 0 < w -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
  (0x10000 <= w /\ w + Z.of_nat (length s) + 8 <= 0x654000 \/ w = WN /\ s = w_name) ->
  bytes_okb (w_rd M) w (s ++ [0]) = true ->
  some_okb (w_rd M) (w + Z.of_nat (length s) + 1) (str_end w s) = true ->
  shadow_okb (w_rd M) w (Z.of_nat (length s) + 1) = true ->
  some_okb (w_rd M) (shadow_addr w / 8 * 8) (shadow_addr (w + (Z.of_nat (length s) + 1) - 1) / 8 * 8 + 8) = true ->
  pf_arg_asan (w_rd M) rs w (APtr s).
Proof.
  intros M K rs s w -> HK Hs Hw0 Hl Hloc Hb Ht Hsh Hh.
  split; [exact Hs|]. split; [exact Hw0|]. split; [exact Hl|].
  split; [intros i Hi; apply bytes_okb_sound; [exact Hb | rewrite len_app1; lia]|].
  split; [intros x Hx; apply (some_okb_sound _ _ _ Ht); lia|].
  assert (HE : str_end w s = w + Z.of_nat (length s) - (w + Z.of_nat (length s)) mod 8 + 8) by reflexivity.
  pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
  split; [|split; [|split; [apply shadow_okb_sound; exact Hsh | apply hull_okb_sound; exact Hh]]].
  - rewrite HE. w_fa; unfold zdisjoint; cbn [fst snd];
      destruct Hloc as [Hloc | (-> & ->)]; rewrite ?len_name in *; cbv [WSP WF WN AMF_BLOCK] in *; lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
    destruct Hloc as [Hloc | (-> & ->)]; rewrite ?len_name in *; cbv [WN] in *; lia.
Qed.

(* the literal / %s / %d pieces of a format, and its precision fact *)
Ltac w_pieces := vm_compute; repeat constructor.

Definition ps_of (fmt : list Z) : list pf_piece := match pf_parse fmt with Some ps => ps | None => [] end.

(* F2 at 0x89aec: k = 0 and |T| = 119, so the text fits the buffer; the format and the name as the image and the
   heap hold them; the family premise over the regions the call writes (the fprintf window LFP_STK and the FILE) *)
Theorem link_fprintf_mf_wit_F2 :
  let m := mrestrict wH0 w_mem_F2 in let rd := w_rd w_mem_F2 in let rs := vmf_out LFP_STK WSP WF in
  amf_k tfibsegs link_amf m WF 0 /\ amf_dyn tfibsegs link_amf m WF AF_NORD 0 0 0 0 0 0 /\
  amf_pend tfibsegs m WF [] /\ Z.of_nat (length (@nil Z)) = 0 /\
  0 + Z.of_nat (length T_F2) <= AMF_BUFSIZ /\ Z.of_nat (length T_F2) < 2 ^ 31 - 1 /\
  pairwise zdisjoint rs /\
  rdword rd LA_GOT_GUARD = Some LA_GUARD /\ rdword rd LA_GUARD = Some WCANARY /\
  Forall (zdisjoint (LA_GOT_GUARD, 8)) rs /\ Forall (zdisjoint (LA_GUARD, 8)) rs /\
  (forall regs, argZ regs 2 = WN -> fva_words regs rd WSP [] (map (argZ regs) [2; 3; 4; 5; 6; 7] ++ []) /\
     pf_family pf_link_piece rd rs STR8 (map (argZ regs) [2; 3; 4; 5; 6; 7] ++ []) T_F2).
Proof.
  cbv zeta. destruct w_file_F2 as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [zc|]. split; [zc|].
  split; [unfold vmf_out; cbn [pairwise]; split; [w_fa; w_zd | split; [apply Forall_nil | exact I]]|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [w_fa; w_zd|]. split; [w_fa; w_zd|].
  intros regs Ha2. split; [split; [reflexivity | intros i Hi; cbn in Hi; lia]|].
  unfold pf_family. exists fmt8, (ps_of fmt8), [APtr w_name].
  split; [|split; [vm_compute; reflexivity|split; [w_pieces|split; [|split; [vm_compute; reflexivity|]]]]].
  - split; [zc|].
    split; [intros i Hi; apply bytes_okb_sound; [vm_compute; reflexivity | rewrite len_app1; lia]|].
    split; [w_fa; w_zd|].
    split; [unfold amem_range, kLowMemEnd, STR8; rewrite len_fmt8; lia|].
    split; [apply shadow_okb_sound; vm_compute; reflexivity | apply hull_okb_sound; vm_compute; reflexivity].
  - cbn [map app pf_args_asan]. rewrite Ha2. split; [|exact I].
    apply (w_string w_mem_F2 LFP_STK); [reflexivity | split; zc | cbv [w_name]; w_fa; cbv beta; lia | zc | zc
      | right; split; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity].
  - apply pf_disco_prec_pos. w_pieces.
Qed.

(* V1 at 0x89d1c: k = 22 (F1's text) and |T| = 147, 22 + 147 <= 1024; the four slots at ap above the window *)
Theorem link_vfprintf_mf_wit_V1 :
  let m := mrestrict wH0 w_mem_V1 in let rd := w_rd w_mem_V1 in let rs := vmf_out LVF_STK WSP WF in
  amf_k tfibsegs link_amf m WF 22 /\
  amf_dyn tfibsegs link_amf m WF AF_NORD AU32M1 (WF + AMF_BUF + AMF_BUFSIZ) (WF + AMF_BUF + 22) (WF + AMF_BUF) 0 0 /\
  amf_pend tfibsegs m WF T_F1 /\ Z.of_nat (length T_F1) = 22 /\
  22 + Z.of_nat (length T_V1) <= AMF_BUFSIZ /\ Z.of_nat (length T_V1) < 2 ^ 31 - 1 /\
  pairwise zdisjoint rs /\
  rdword rd LA_GOT_GUARD = Some LA_GUARD /\ rdword rd LA_GUARD = Some WCANARY /\
  Forall (zdisjoint (LA_GOT_GUARD, 8)) rs /\ Forall (zdisjoint (LA_GUARD, 8)) rs /\
  words_at rd WAP w_slots /\ WSP <= WAP /\ WAP + 8 * Z.of_nat (length w_slots) <= 2 ^ 47 /\
  Forall (zdisjoint (WAP, 8 * Z.of_nat (length w_slots))) rs /\
  pf_family pf_link_piece rd rs STR5 w_slots T_V1.
Proof.
  cbv zeta. destruct w_file_V1 as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [zc|]. split; [zc|].
  split; [unfold vmf_out; cbn [pairwise]; split; [w_fa; w_zd | split; [apply Forall_nil | exact I]]|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [w_fa; w_zd|]. split; [w_fa; w_zd|].
  split; [apply words_okb_sound; vm_compute; reflexivity|].
  split; [zc|]. split; [zc|].
  split; [w_fa; w_zd|].
  unfold pf_family. exists fmt5, (ps_of fmt5), [APtr w_name; APtr str4; AInt 1; APtr str6].
  split; [|split; [vm_compute; reflexivity|split; [w_pieces|split; [|split; [vm_compute; reflexivity|]]]]].
  - split; [zc|].
    split; [intros i Hi; apply bytes_okb_sound; [vm_compute; reflexivity | rewrite len_app1; lia]|].
    split; [w_fa; w_zd|].
    split; [unfold amem_range, kLowMemEnd, STR5; rewrite len_fmt5; lia|].
    split; [apply shadow_okb_sound; vm_compute; reflexivity | apply hull_okb_sound; vm_compute; reflexivity].
  - cbn [pf_args_asan w_slots].
    split; [apply (w_string w_mem_V1 LVF_STK); [reflexivity | split; zc | cbv [w_name]; w_fa; cbv beta; lia | zc | zc
      | right; split; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity]|].
    split; [apply (w_string w_mem_V1 LVF_STK); [reflexivity | split; zc | cbv [str4]; w_fa; cbv beta; lia | zc | zc
      | left; split; zc | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity]|].
    split; [split; [split; zc | reflexivity]|].
    split; [apply (w_string w_mem_V1 LVF_STK); [reflexivity | split; zc | cbv [str6]; w_fa; cbv beta; lia | zc | zc
      | left; split; zc | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity]|].
    exact I.
  - apply pf_disco_prec_pos. w_pieces.
Qed.

(* ---- the read-only invariant at the callers' relro bounds: the witness memory adds no byte below 0xa3000, where
   every read-only byte lies, so each one reads as the image ---- *)
Lemma w_ro_low : forall a, in_roP tfibsegs PCAP_RLO PCAP_RHI a -> 0 <= a < 0xa3000.
Proof.
  intros a [(s & Hin & Hw & Ha) | Ha]; [| unfold PCAP_RLO, PCAP_RHI in Ha; lia].
  assert (H : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa3000))%bool
                tfibsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). rewrite Hw in H. cbn [orb] in H. apply Z.leb_le in H. lia.
Qed.

Lemma w_base_low : forall b a, 0 <= a < 0xa3000 -> w_base b (Z_to_bv 64 a) = None.
Proof.
  intros b a Ha. unfold w_base. cbv zeta. rewrite (amf_unsigned64 a) by lia.
  replace (kLowShadowBeg <=? a) with false by (symmetry; apply Z.leb_gt; unfold kLowShadowBeg; lia).
  replace (WN <=? a) with false by (symmetry; apply Z.leb_gt; unfold WN; lia).
  replace (WAP <=? a) with false by (symmetry; apply Z.leb_gt; unfold WAP, WSP; lia).
  replace (LA_GUARD <=? a) with false by (symmetry; apply Z.leb_gt; unfold LA_GUARD; lia).
  replace (WF + AMF_BUF <=? a) with false by (symmetry; apply Z.leb_gt; unfold WF, AMF_BUF; lia).
  destruct b; reflexivity.
Qed.

Lemma w_state_low : forall M fl om wend wpos wbase pos len a, 0 <= a < 0xa3000 ->
  mbyte tfibsegs (amf_state link_amf M WF fl om wend wpos wbase pos len) a = mbyte tfibsegs M a.
Proof.
  intros M fl om wend wpos wbase pos len a Ha. unfold amf_state, amf_heads_set.
  rewrite !amf_upd_out by (cbv [link_amf amf_sink_addr amf_say_addr amf_ofl_head amf_ofl_lock];
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite (amf_dynw_out tfibsegs) by (unfold WF, AMF_ZEROED; lia).
  rewrite (amf_fm_out tfibsegs link_amf) by (unfold WF, AMF_ZEROED; lia).
  reflexivity.
Qed.

Lemma mbyte_wH0 : forall M a, mbyte tfibsegs (mrestrict wH0 M) a = mbyte tfibsegs M a.
Proof. reflexivity. Qed.

Lemma link_vf_wit_arodata : forall B,
  arodata_okP tfibsegs PCAP_RLO PCAP_RHI B (w_rd w_mem_F2) /\ arodata_okP tfibsegs PCAP_RLO PCAP_RHI B (w_rd w_mem_V1).
Proof.
  intros B. split; intros a Ha _ _; pose proof (w_ro_low a Ha) as L; unfold w_rd, aview; rewrite mbyte_wH0;
    [unfold w_mem_F2 | unfold w_mem_V1]; rewrite w_state_low by exact L; unfold mbyte; rewrite w_base_low by exact L;
    reflexivity.
Qed.
