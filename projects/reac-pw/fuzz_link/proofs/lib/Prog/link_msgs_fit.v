(* reac-pw/fuzz_link, PLAIN build: every line link's marking code prints fits the 1024-byte buffer of
   link's memory FILE at its call site (W2-printf.md deliverable 8: the fit premise of the vfprintf and
   fprintf contracts, `k + |T| <= MemFile.MF_BUFSIZ`).

   The lines (link/donors/REPORT.md section 2; sources link/src/reac_served_mark.c:48-92 and
   libreac include/reac/reac_code.h:101-109; disassembly link/ct/dis/plain/reac_served_mark.s and
   reac_code_emit.s). Each format and each constant argument below is the byte list the image holds at
   its address (checked by vm_compute over the image's segments, `fmt_ok` / `str_ok`), and each was
   compared with the C source text (the same bytes; the dash is UTF-8 E2 80 94):
   - reac_code_emit 0x16684 (+0x44): fprintf(f, "%s: %s ", "reac-pw", "E_NOT_MARKED"): the format at
     0x10558 (+0x34 a1), "reac-pw" at 0x10520 (+0x38 a2), "E_NOT_MARKED" at 0x103a8 (+0x3c a3). The
     compiler folded reac_code_emit's prog and code arguments: these three addresses are its own.
   - reac_code_emit 0x1669c (+0x5c): vfprintf(f, fmt, ap) with
     . fmt 0x105a1 from reac_served_mark 0x164e0 (+0x70; source :55-58), args a4 = ifname,
       a5 = negw s1 (the int32 -rc): "[%s] could not read the interface alias (errno %d) ...\n";
     . fmt 0x103c2 from reac_served_mark 0x16628 (+0x1b8; source :66-70), args a4 = ifname,
       a5 = 0x10341 "reac-pw:served", a6 = negw s1, a7 = 0x1043b ": this daemon has no CAP_NET_ADMIN"
       when rc = -1 (+0xec beq s1,-1; +0x1ac) and 0x10368 "" otherwise (+0xf4).
   - reac_served_mark 0x16598 (+0x128): fprintf(f, 0x102b3, ifname) (verdict LEAVE_VLAN, source :82-83).
   - reac_served_mark 0x165f8 (+0x188): fprintf(f, 0x1049d, ifname, alias) (LEAVE_HOST, source :86-88),
     alias = sp, the char alias[256] of reac_served_mark's frame (source :52), so at most 255 bytes.
   Pending bytes k at each call: mark_quietly rewinds the FILE before every mark (fuzz_link.c:162), so
   reac_served_mark's own fprintf calls and reac_code_emit's fprintf start at k = 0; reac_code_emit's
   vfprintf starts after the 22 bytes "reac-pw: E_NOT_MARKED " (`emit_code_len`).
   IFN = 652 is the largest bound on the interface name's length for which every line fits: the
   LEAVE_HOST line is 117 literal bytes + ifname + alias (<= 255), and 117 + 652 + 255 = 1024
   (`ifn_largest` shows a 653-byte name overflows it). The harness gives a name of at most 11 bytes
   (fuzz_link.c name_of: g_names "nl0".."nl63", or the `odd` table, longest "enp131s0.33"). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Image.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Printf_model.
Local Open Scope Z_scope.

(* ==========================================================================
   1. A format and a constant string in the image
   ========================================================================== *)

Lemma forall_bytes : forall l, forallb (fun c => (0 <=? c) && (c <? 256)) l = true ->
  Forall (fun c => 0 <= c < 256) l.
Proof.
  intros l H. apply Forall_forall. intros c Hc. rewrite forallb_forall in H. specialize (H c Hc).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma forall_bytes_pos : forall l, forallb (fun c => (0 <? c) && (c <? 256)) l = true ->
  Forall (fun c => 0 < c < 256) l.
Proof.
  intros l H. apply Forall_forall. intros c Hc. rewrite forallb_forall in H. specialize (H c Hc).
  apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* What the vfprintf / fprintf contracts and CJ's printf_core take of a format at A: its bytes and the
   NUL in every memory that keeps the image's read-only bytes, the address in .rodata, the pieces
   `pf_parse` reads, CJ's first-pass check, and every byte below 256. *)
Definition fmt_ok (A : Z) (fmt : list Z) (ps : list pf_piece) : Prop :=
  (forall m, mem_inv rsegs m -> bytes_at rsegs m A (pf_bytes (fmt ++ [0]))) /\
  RO_LO <= A /\ A + Z.of_nat (length fmt) + 1 <= RO_END /\
  pf_parse fmt = Some ps /\
  Printf_model.pass1_ok (fmt ++ [0]) = true /\
  Forall (fun c => 0 <= c < 256) (fmt ++ [0]).

Lemma fmt_ok_of : forall A fmt ps,
  ro_bytes_b rsegs A (pf_bytes (fmt ++ [0])) = true ->
  (RO_LO <=? A) && (A + Z.of_nat (length fmt) + 1 <=? RO_END) = true ->
  pf_parse fmt = Some ps -> Printf_model.pass1_ok (fmt ++ [0]) = true ->
  forallb (fun c => (0 <=? c) && (c <? 256)) (fmt ++ [0]) = true ->
  fmt_ok A fmt ps.
Proof.
  intros A fmt ps Hb Hr Hp H1 Hf. apply andb_prop in Hr as [Hr1 Hr2].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
  split; [|split; [exact Hr1|split; [exact Hr2|split; [exact Hp|split; [exact H1|]]]]].
  - intros m Hm. apply ro_bytes_at; [exact Hm | unfold RO_LO in Hr1; lia | |].
    + assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
      unfold pf_bytes. rewrite length_map, length_app. cbn [length]. unfold RO_END in Hr2. lia.
    + apply ro_bytes_b_sound. exact Hb.
  - apply forall_bytes. exact Hf.
Qed.

(* What printf_facts_c's `pf_arg_ok` takes of a constant string argument at A: its bytes, its NUL and
   the `slack` bytes after it up to the next multiple of 8, the address in .rodata, every byte of the
   string in 1..255. *)
Definition str_ok (A : Z) (s slack : list Z) : Prop :=
  (forall m, mem_inv rsegs m -> bytes_at rsegs m A (pf_bytes (s ++ [0]) ++ pf_bytes slack)) /\
  (- (A + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
  RO_LO <= A /\ A + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= RO_END /\
  Forall (fun c => 0 < c < 256) s.

Lemma str_ok_of : forall A s slack,
  ro_bytes_b rsegs A (pf_bytes (s ++ [0]) ++ pf_bytes slack) = true ->
  ((- (A + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length slack)) && (RO_LO <=? A) &&
  (A + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <=? RO_END) = true ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  str_ok A s slack.
Proof.
  intros A s slack Hb Hr Hf. apply andb_prop in Hr as [Hr Hr3]. apply andb_prop in Hr as [Hr1 Hr2].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr2. apply Z.leb_le in Hr3.
  split; [|split; [exact Hr1|split; [exact Hr2|split; [exact Hr3|apply forall_bytes_pos; exact Hf]]]].
  intros m Hm. apply ro_bytes_at; [exact Hm | unfold RO_LO in Hr2; lia | |].
  - assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
    unfold pf_bytes. rewrite length_app, !length_map, length_app. cbn [length]. unfold RO_END in Hr3. lia.
  - apply ro_bytes_b_sound. exact Hb.
Qed.

(* ==========================================================================
   2. The length of a text from %s, %d and literal bytes
   ========================================================================== *)

(* the pieces link's formats use *)
Definition pc_lds (p : pf_piece) : bool :=
  match p with PLit _ | Pd | Ps => true | _ => false end.

(* the literal bytes of a format *)
Fixpoint pf_lits (ps : list pf_piece) : Z :=
  match ps with
  | [] => 0
  | PLit _ :: r => 1 + pf_lits r
  | _ :: r => pf_lits r
  end.

(* the bytes an argument prints under %d (AInt) or %s (APtr) *)
Definition pa_len (a : pf_arg) : Z :=
  match a with
  | AInt v => Z.of_nat (length (pf_dec v))
  | AU64 u => Z.of_nat (length (pf_udec u))
  | APtr s => Z.of_nat (length s)
  end.

Fixpoint pa_lens (args : list pf_arg) : Z :=
  match args with [] => 0 | a :: r => pa_len a + pa_lens r end.

Lemma pf_text_length : forall ps args T, forallb pc_lds ps = true -> pf_text ps args = Some T ->
  Z.of_nat (length T) = pf_lits ps + pa_lens args.
Proof.
  induction ps as [|p ps IH]; intros args T Hl Ht.
  - destruct args as [|a args]; cbn [pf_text] in Ht; [|discriminate Ht].
    injection Ht as <-. reflexivity.
  - cbn [forallb] in Hl. apply andb_prop in Hl as [Hp Hl].
    destruct p; cbn [pc_lds] in Hp; try discriminate Hp.
    + cbn [pf_text] in Ht.
      destruct (pf_text ps args) as [T'|] eqn:E; cbn [option_map] in Ht; [|discriminate Ht].
      injection Ht as <-. pose proof (IH args T' Hl E) as L. cbn [length pf_lits]. lia.
    + destruct args as [|[v|u|s] args]; cbn [pf_text] in Ht; try discriminate Ht.
      destruct (pf_text ps args) as [T'|] eqn:E; cbn [option_map] in Ht; [|discriminate Ht].
      injection Ht as <-. pose proof (IH args T' Hl E) as L. rewrite length_app.
      cbn [pa_lens pa_len pf_lits]. lia.
    + destruct args as [|[v|u|s] args]; cbn [pf_text] in Ht; try discriminate Ht.
      destruct (pf_text ps args) as [T'|] eqn:E; cbn [option_map] in Ht; [|discriminate Ht].
      injection Ht as <-. pose proof (IH args T' Hl E) as L. rewrite length_app.
      cbn [pa_lens pa_len pf_lits]. lia.
Qed.

Lemma pf_digits_len : forall fuel x acc n, 0 <= x < 10 ^ n -> 1 <= n ->
  Z.of_nat (length (pf_digits fuel x acc)) <= Z.of_nat (length acc) + n.
Proof.
  induction fuel as [|fuel IH]; intros x acc n Hx Hn; cbn [pf_digits]; [lia|].
  destruct (Z.ltb_spec x 10) as [H|H]; [cbn [length]; lia|].
  assert (Hn2 : 2 <= n).
  { destruct (Z_le_gt_dec 2 n) as [H2|H2]; [exact H2|].
    assert (E1 : n = 1) by lia. subst n. cbn in Hx. lia. }
  assert (E : 10 ^ n = 10 * 10 ^ (n - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (Hd : 0 <= x / 10 < 10 ^ (n - 1)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  pose proof (IH (x / 10) ((48 + x mod 10) :: acc) (n - 1) Hd ltac:(lia)) as L.
  cbn [length] in L. lia.
Qed.

(* %d of an int32 prints at most 11 bytes (the sign and ten digits) *)
Lemma pf_dec_len : forall v, -2^31 <= v < 2^31 -> Z.of_nat (length (pf_dec v)) <= 11.
Proof.
  intros v Hv. assert (P : 2 ^ 31 = 2147483648) by reflexivity.
  assert (Q : 10 ^ 10 = 10000000000) by reflexivity.
  unfold pf_dec. destruct (Z.ltb_spec v 0) as [H|H].
  - pose proof (pf_digits_len 11 (- v) [] 10 ltac:(lia) ltac:(lia)) as L. cbn [length] in *. lia.
  - pose proof (pf_digits_len 11 v [] 10 ltac:(lia) ltac:(lia)) as L. cbn [length] in *. lia.
Qed.

(* ==========================================================================
   3. The formats and the constant arguments, read from the image
   ========================================================================== *)

Definition ps_of (fmt : list Z) : list pf_piece :=
  match pf_parse fmt with Some ps => ps | None => [] end.
(* "%s: %s " (reac_code_emit +0x34) *)
Definition FMT_EMIT_A : Z := 0x10558.
Definition FMT_EMIT : list Z :=
  [37; 115; 58; 32; 37; 115; 32].
Definition PS_EMIT : list pf_piece := Eval vm_compute in ps_of FMT_EMIT.
Lemma fmt_emit_ok : fmt_ok FMT_EMIT_A FMT_EMIT PS_EMIT.
Proof. apply fmt_ok_of; vm_compute; reflexivity. Qed.
Lemma fmt_emit_lds : forallb pc_lds PS_EMIT = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt_emit_lits : pf_lits PS_EMIT = 3.
Proof. vm_compute. reflexivity. Qed.

(* "reac-pw" (reac_code_emit +0x38) *)
Definition S_REACPW_A : Z := 0x10520.
Definition S_REACPW : list Z := [114; 101; 97; 99; 45; 112; 119].
Lemma s_reacpw_ok : str_ok S_REACPW_A S_REACPW [].
Proof. apply str_ok_of; vm_compute; reflexivity. Qed.
Lemma s_reacpw_len : length S_REACPW = 7%nat.
Proof. reflexivity. Qed.

(* "E_NOT_MARKED" (reac_code_emit +0x3c) *)
Definition S_ENM_A : Z := 0x103a8.
Definition S_ENM : list Z := [69; 95; 78; 79; 84; 95; 77; 65; 82; 75; 69; 68].
Lemma s_enm_ok : str_ok S_ENM_A S_ENM [105; 110; 102].
Proof. apply str_ok_of; vm_compute; reflexivity. Qed.
Lemma s_enm_len : length S_ENM = 12%nat.
Proof. reflexivity. Qed.

(* "[%s] could not read the interface alias (errno %d) — not marked as a REAC interface, so the host's network manager is not told to leave it alone\n" (reac_served_mark +0x70, source :56-58) *)
Definition FMT_READ_A : Z := 0x105a1.
Definition FMT_READ : list Z :=
  [91; 37; 115; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 114; 101; 97; 100; 32; 116; 104;
   101; 32; 105; 110; 116; 101; 114; 102; 97; 99; 101; 32; 97; 108; 105; 97; 115; 32; 40; 101; 114; 114;
   110; 111; 32; 37; 100; 41; 32; 226; 128; 148; 32; 110; 111; 116; 32; 109; 97; 114; 107; 101; 100; 32;
   97; 115; 32; 97; 32; 82; 69; 65; 67; 32; 105; 110; 116; 101; 114; 102; 97; 99; 101; 44; 32; 115; 111;
   32; 116; 104; 101; 32; 104; 111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109;
   97; 110; 97; 103; 101; 114; 32; 105; 115; 32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111;
   32; 108; 101; 97; 118; 101; 32; 105; 116; 32; 97; 108; 111; 110; 101; 10].
Definition PS_READ : list pf_piece := Eval vm_compute in ps_of FMT_READ.
Lemma fmt_read_ok : fmt_ok FMT_READ_A FMT_READ PS_READ.
Proof. apply fmt_ok_of; vm_compute; reflexivity. Qed.
Lemma fmt_read_lds : forallb pc_lds PS_READ = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt_read_lits : pf_lits PS_READ = 143.
Proof. vm_compute. reflexivity. Qed.

(* "[%s] could not mark it '%s' (errno %d)%s — the host's network manager is not told to leave it alone\n" (reac_served_mark +0x1b8, source :67-68) *)
Definition FMT_MARK_A : Z := 0x103c2.
Definition FMT_MARK : list Z :=
  [91; 37; 115; 93; 32; 99; 111; 117; 108; 100; 32; 110; 111; 116; 32; 109; 97; 114; 107; 32; 105; 116;
   32; 39; 37; 115; 39; 32; 40; 101; 114; 114; 110; 111; 32; 37; 100; 41; 37; 115; 32; 226; 128; 148;
   32; 116; 104; 101; 32; 104; 111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109;
   97; 110; 97; 103; 101; 114; 32; 105; 115; 32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111;
   32; 108; 101; 97; 118; 101; 32; 105; 116; 32; 97; 108; 111; 110; 101; 10].
Definition PS_MARK : list pf_piece := Eval vm_compute in ps_of FMT_MARK.
Lemma fmt_mark_ok : fmt_ok FMT_MARK_A FMT_MARK PS_MARK.
Proof. apply fmt_ok_of; vm_compute; reflexivity. Qed.
Lemma fmt_mark_lds : forallb pc_lds PS_MARK = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt_mark_lits : pf_lits PS_MARK = 94.
Proof. vm_compute. reflexivity. Qed.

(* "reac-pw:served" (REAC_SERVED_ALIAS; reac_served_mark +0x1bc, a5) *)
Definition S_SERVED_A : Z := 0x10341.
Definition S_SERVED : list Z := [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100].
Lemma s_served_ok : str_ok S_SERVED_A S_SERVED [].
Proof. apply str_ok_of; vm_compute; reflexivity. Qed.
Lemma s_served_len : length S_SERVED = 14%nat.
Proof. reflexivity. Qed.

(* ": this daemon has no CAP_NET_ADMIN" (reac_served_mark +0x1ac, a7, when rc = -EPERM = -1; source :70) *)
Definition S_CAP_A : Z := 0x1043b.
Definition S_CAP : list Z := [58; 32; 116; 104; 105; 115; 32; 100; 97; 101; 109; 111; 110; 32; 104; 97; 115; 32; 110; 111; 32; 67;
   65; 80; 95; 78; 69; 84; 95; 65; 68; 77; 73; 78].
Lemma s_cap_ok : str_ok S_CAP_A S_CAP [73; 78].
Proof. apply str_ok_of; vm_compute; reflexivity. Qed.
Lemma s_cap_len : length S_CAP = 34%nat.
Proof. reflexivity. Qed.

(* "" (reac_served_mark +0xf4, a7, when rc <> -1; source :70) *)
Definition S_EMPTY_A : Z := 0x10368.
Definition S_EMPTY : list Z := [].
Lemma s_empty_ok : str_ok S_EMPTY_A S_EMPTY [46; 0; 117; 115; 97; 103; 101].
Proof. apply str_ok_of; vm_compute; reflexivity. Qed.
Lemma s_empty_len : length S_EMPTY = 0%nat.
Proof. reflexivity. Qed.

(* "reac-pw: [%s] is a VLAN the host made — not marked; if a network manager configures it, give it no addresses there\n" (reac_served_mark +0x120, source :82-83) *)
Definition FMT_VLAN_A : Z := 0x102b3.
Definition FMT_VLAN : list Z :=
  [114; 101; 97; 99; 45; 112; 119; 58; 32; 91; 37; 115; 93; 32; 105; 115; 32; 97; 32; 86; 76; 65; 78;
   32; 116; 104; 101; 32; 104; 111; 115; 116; 32; 109; 97; 100; 101; 32; 226; 128; 148; 32; 110; 111;
   116; 32; 109; 97; 114; 107; 101; 100; 59; 32; 105; 102; 32; 97; 32; 110; 101; 116; 119; 111; 114;
   107; 32; 109; 97; 110; 97; 103; 101; 114; 32; 99; 111; 110; 102; 105; 103; 117; 114; 101; 115; 32;
   105; 116; 44; 32; 103; 105; 118; 101; 32; 105; 116; 32; 110; 111; 32; 97; 100; 100; 114; 101; 115;
   115; 101; 115; 32; 116; 104; 101; 114; 101; 10].
Definition PS_VLAN : list pf_piece := Eval vm_compute in ps_of FMT_VLAN.
Lemma fmt_vlan_ok : fmt_ok FMT_VLAN_A FMT_VLAN PS_VLAN.
Proof. apply fmt_ok_of; vm_compute; reflexivity. Qed.
Lemma fmt_vlan_lds : forallb pc_lds PS_VLAN = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt_vlan_lits : pf_lits PS_VLAN = 115.
Proof. vm_compute. reflexivity. Qed.

(* "reac-pw: [%s] carries the host's own alias '%s' — not marked; the host's network manager is not told to leave it alone\n" (reac_served_mark +0x17c, source :86-88) *)
Definition FMT_HOST_A : Z := 0x1049d.
Definition FMT_HOST : list Z :=
  [114; 101; 97; 99; 45; 112; 119; 58; 32; 91; 37; 115; 93; 32; 99; 97; 114; 114; 105; 101; 115; 32;
   116; 104; 101; 32; 104; 111; 115; 116; 39; 115; 32; 111; 119; 110; 32; 97; 108; 105; 97; 115; 32; 39;
   37; 115; 39; 32; 226; 128; 148; 32; 110; 111; 116; 32; 109; 97; 114; 107; 101; 100; 59; 32; 116; 104;
   101; 32; 104; 111; 115; 116; 39; 115; 32; 110; 101; 116; 119; 111; 114; 107; 32; 109; 97; 110; 97;
   103; 101; 114; 32; 105; 115; 32; 110; 111; 116; 32; 116; 111; 108; 100; 32; 116; 111; 32; 108; 101;
   97; 118; 101; 32; 105; 116; 32; 97; 108; 111; 110; 101; 10].
Definition PS_HOST : list pf_piece := Eval vm_compute in ps_of FMT_HOST.
Lemma fmt_host_ok : fmt_ok FMT_HOST_A FMT_HOST PS_HOST.
Proof. apply fmt_ok_of; vm_compute; reflexivity. Qed.
Lemma fmt_host_lds : forallb pc_lds PS_HOST = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt_host_lits : pf_lits PS_HOST = 117.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   4. The length of each line
   ========================================================================== *)

(* reac_code_emit's own line: "reac-pw: E_NOT_MARKED ", 22 bytes *)
Definition T_EMIT : list Z := Eval vm_compute in
  match pf_text PS_EMIT [APtr S_REACPW; APtr S_ENM] with Some T => T | None => [] end.

Lemma text_emit : pf_text PS_EMIT [APtr S_REACPW; APtr S_ENM] = Some T_EMIT.
Proof. vm_compute. reflexivity. Qed.

Lemma emit_code_len : forall T, pf_text PS_EMIT [APtr S_REACPW; APtr S_ENM] = Some T ->
  Z.of_nat (length T) = 22.
Proof. intros T H. rewrite text_emit in H. injection H as <-. reflexivity. Qed.

Lemma len_read : forall ifname rc T, -2^31 <= rc < 2^31 ->
  pf_text PS_READ [APtr ifname; AInt rc] = Some T ->
  Z.of_nat (length T) <= 143 + Z.of_nat (length ifname) + 11.
Proof.
  intros ifname rc T Hr H. pose proof (pf_text_length _ _ _ fmt_read_lds H) as L.
  pose proof (pf_dec_len rc Hr) as D. rewrite fmt_read_lits in L. cbn [pa_lens pa_len] in L. lia.
Qed.

Lemma len_mark : forall ifname rc cap T, -2^31 <= rc < 2^31 ->
  pf_text PS_MARK [APtr ifname; APtr S_SERVED; AInt rc; APtr cap] = Some T ->
  Z.of_nat (length T) <= 94 + Z.of_nat (length ifname) + 14 + 11 + Z.of_nat (length cap).
Proof.
  intros ifname rc cap T Hr H. pose proof (pf_text_length _ _ _ fmt_mark_lds H) as L.
  pose proof (pf_dec_len rc Hr) as D. rewrite fmt_mark_lits in L. cbn [pa_lens pa_len] in L.
  rewrite s_served_len in L. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in L. lia.
Qed.

Lemma len_vlan : forall ifname T, pf_text PS_VLAN [APtr ifname] = Some T ->
  Z.of_nat (length T) = 115 + Z.of_nat (length ifname).
Proof.
  intros ifname T H. pose proof (pf_text_length _ _ _ fmt_vlan_lds H) as L.
  rewrite fmt_vlan_lits in L. cbn [pa_lens pa_len] in L. lia.
Qed.

Lemma len_host : forall ifname alias T, pf_text PS_HOST [APtr ifname; APtr alias] = Some T ->
  Z.of_nat (length T) = 117 + Z.of_nat (length ifname) + Z.of_nat (length alias).
Proof.
  intros ifname alias T H. pose proof (pf_text_length _ _ _ fmt_host_lds H) as L.
  rewrite fmt_host_lits in L. cbn [pa_lens pa_len] in L. lia.
Qed.

(* ==========================================================================
   5. Every line fits at its call site
   ========================================================================== *)

(* the largest length of the interface name for which every line fits *)
Definition IFN : Z := 652.

Lemma mf_bufsiz_1024 : MemFile.MF_BUFSIZ = 1024.
Proof. reflexivity. Qed.

(* reac_code_emit 0x16684 (+0x44): fprintf(f, FMT_EMIT, S_REACPW, S_ENM), k = 0 *)
Lemma fit_emit_code : forall (ifname alias : list Z) (rc : Z) (T : list Z), Z.of_nat (length ifname) <= IFN ->
  Z.of_nat (length alias) <= 255 -> -2^31 <= rc < 2^31 ->
  pf_text PS_EMIT [APtr S_REACPW; APtr S_ENM] = Some T -> 0 + Z.of_nat (length T) <= MemFile.MF_BUFSIZ.
Proof.
  intros ifname alias rc T _ _ _ H. rewrite (emit_code_len T H). unfold MemFile.MF_BUFSIZ. lia.
Qed.

(* reac_code_emit 0x1669c (+0x5c): vfprintf(f, FMT_READ, ap), ap = [ifname; -rc], from reac_served_mark
   0x164ec; k = 22 *)
Lemma fit_emit_read : forall (ifname alias : list Z) (rc : Z) (T : list Z), Z.of_nat (length ifname) <= IFN ->
  Z.of_nat (length alias) <= 255 -> -2^31 <= rc < 2^31 ->
  pf_text PS_READ [APtr ifname; AInt rc] = Some T -> 22 + Z.of_nat (length T) <= MemFile.MF_BUFSIZ.
Proof.
  intros ifname alias rc T Hi _ Hr H. pose proof (len_read ifname rc T Hr H) as L.
  unfold IFN, MemFile.MF_BUFSIZ in *. lia.
Qed.

(* reac_code_emit 0x1669c (+0x5c): vfprintf(f, FMT_MARK, ap), ap = [ifname; S_SERVED; -rc; cap] with
   cap = S_CAP or S_EMPTY, from reac_served_mark 0x16638; k = 22 *)
Lemma fit_emit_mark : forall (ifname alias : list Z) (rc : Z) (cap T : list Z), Z.of_nat (length ifname) <= IFN ->
  Z.of_nat (length alias) <= 255 -> -2^31 <= rc < 2^31 -> cap = S_CAP \/ cap = S_EMPTY ->
  pf_text PS_MARK [APtr ifname; APtr S_SERVED; AInt rc; APtr cap] = Some T ->
  22 + Z.of_nat (length T) <= MemFile.MF_BUFSIZ.
Proof.
  intros ifname alias rc cap T Hi _ Hr Hc H. pose proof (len_mark ifname rc cap T Hr H) as L.
  assert (Hcl : Z.of_nat (length cap) <= 34).
  { destruct Hc as [->| ->]; [rewrite s_cap_len | rewrite s_empty_len]; cbn; lia. }
  unfold IFN, MemFile.MF_BUFSIZ in *. lia.
Qed.

(* reac_served_mark 0x16598 (+0x128): fprintf(f, FMT_VLAN, ifname), k = 0 *)
Lemma fit_mark_vlan : forall (ifname alias : list Z) (rc : Z) (T : list Z), Z.of_nat (length ifname) <= IFN ->
  Z.of_nat (length alias) <= 255 -> -2^31 <= rc < 2^31 ->
  pf_text PS_VLAN [APtr ifname] = Some T -> 0 + Z.of_nat (length T) <= MemFile.MF_BUFSIZ.
Proof.
  intros ifname alias rc T Hi _ _ H. pose proof (len_vlan ifname T H) as L.
  unfold IFN, MemFile.MF_BUFSIZ in *. lia.
Qed.

(* reac_served_mark 0x165f8 (+0x188): fprintf(f, FMT_HOST, ifname, alias), k = 0 *)
Lemma fit_mark_host : forall (ifname alias : list Z) (rc : Z) (T : list Z), Z.of_nat (length ifname) <= IFN ->
  Z.of_nat (length alias) <= 255 -> -2^31 <= rc < 2^31 ->
  pf_text PS_HOST [APtr ifname; APtr alias] = Some T -> 0 + Z.of_nat (length T) <= MemFile.MF_BUFSIZ.
Proof.
  intros ifname alias rc T Hi Ha _ H. pose proof (len_host ifname alias T H) as L.
  unfold IFN, MemFile.MF_BUFSIZ in *. lia.
Qed.

(* IFN is the largest such bound: with a name of IFN + 1 bytes and an alias of 255, the LEAVE_HOST
   line is 1025 bytes. *)
Lemma ifn_largest : exists ifname alias T,
  Z.of_nat (length ifname) = IFN + 1 /\ Z.of_nat (length alias) <= 255 /\
  pf_text PS_HOST [APtr ifname; APtr alias] = Some T /\ MemFile.MF_BUFSIZ < 0 + Z.of_nat (length T).
Proof.
  exists (repeat 97 653), (repeat 97 255).
  assert (H : match pf_text PS_HOST [APtr (repeat 97 653); APtr (repeat 97 255)] with
              | Some T => MemFile.MF_BUFSIZ < 0 + Z.of_nat (length T)
              | None => False
              end) by (vm_compute; reflexivity).
  destruct (pf_text PS_HOST [APtr (repeat 97 653); APtr (repeat 97 255)]) as [T|]; [|destruct H].
  exists T. rewrite !repeat_length. unfold IFN. split; [reflexivity|]. split; [lia|]. split; [reflexivity | exact H].
Qed.
