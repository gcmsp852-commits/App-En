// zxing_qrcrypt_patch.js
// 目的：第2QRが暗号化されていてZXingが通常 decode できないケースで、
//      「コード語抽出→XOR復号→RS復号→データ解釈」の順に通すための拡張。

window.QRCRYPT = (() => {

  // =========================
  // SHA-256（同期・純JS実装）
  // =========================
  // ※WebCrypto(subtle.digest) は async になるので、ここでは同期版を内蔵します。
  function sha256Bytes(msgBytes) {
    const K = new Uint32Array([
      0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
      0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
      0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
      0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
      0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
      0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
      0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
      0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
    ]);

    const ROTR = (x, n) => (x >>> n) | (x << (32 - n));
    const Ch   = (x, y, z) => (x & y) ^ (~x & z);
    const Maj  = (x, y, z) => (x & y) ^ (x & z) ^ (y & z);
    const Sig0 = (x) => ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22);
    const Sig1 = (x) => ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25);
    const sig0 = (x) => ROTR(x, 7) ^ ROTR(x, 18) ^ (x >>> 3);
    const sig1 = (x) => ROTR(x, 17) ^ ROTR(x, 19) ^ (x >>> 10);

    const msg = msgBytes instanceof Uint8Array ? msgBytes : new Uint8Array(msgBytes);
    const l = msg.length;
    const bitLenHi = Math.floor((l * 8) / 0x100000000);
    const bitLenLo = (l * 8) >>> 0;

    // padding
    const with1 = l + 1;
    const padLen = (with1 % 64 <= 56) ? (56 - (with1 % 64)) : (56 + 64 - (with1 % 64));
    const totalLen = l + 1 + padLen + 8;

    const buf = new Uint8Array(totalLen);
    buf.set(msg, 0);
    buf[l] = 0x80;
    // last 8 bytes = big-endian 64-bit length
    const dv = new DataView(buf.buffer);
    dv.setUint32(totalLen - 8, bitLenHi);
    dv.setUint32(totalLen - 4, bitLenLo);

    // initial hash
    let h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a;
    let h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19;

    const W = new Uint32Array(64);

    for (let off = 0; off < totalLen; off += 64) {
      // message schedule
      for (let i = 0; i < 16; i++) {
        const p = off + i * 4;
        W[i] = ((buf[p] << 24) | (buf[p + 1] << 16) | (buf[p + 2] << 8) | (buf[p + 3])) >>> 0;
      }
      for (let i = 16; i < 64; i++) {
        W[i] = (sig1(W[i - 2]) + W[i - 7] + sig0(W[i - 15]) + W[i - 16]) >>> 0;
      }

      // compression
      let a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, h = h7;

      for (let i = 0; i < 64; i++) {
        const T1 = (h + Sig1(e) + Ch(e, f, g) + K[i] + W[i]) >>> 0;
        const T2 = (Sig0(a) + Maj(a, b, c)) >>> 0;
        h = g;
        g = f;
        f = e;
        e = (d + T1) >>> 0;
        d = c;
        c = b;
        b = a;
        a = (T1 + T2) >>> 0;
      }

      h0 = (h0 + a) >>> 0;
      h1 = (h1 + b) >>> 0;
      h2 = (h2 + c) >>> 0;
      h3 = (h3 + d) >>> 0;
      h4 = (h4 + e) >>> 0;
      h5 = (h5 + f) >>> 0;
      h6 = (h6 + g) >>> 0;
      h7 = (h7 + h) >>> 0;
    }

    const out = new Uint8Array(32);
    const words = [h0,h1,h2,h3,h4,h5,h6,h7];
    for (let i = 0; i < 8; i++) {
      out[i*4+0] = (words[i] >>> 24) & 0xff;
      out[i*4+1] = (words[i] >>> 16) & 0xff;
      out[i*4+2] = (words[i] >>>  8) & 0xff;
      out[i*4+3] = (words[i] >>>  0) & 0xff;
    }
    return out;
  }

  function utf8Bytes(str){ return new TextEncoder().encode(String(str ?? "")); }

  function deriveMask(password, neededBytes){
    const out = new Uint8Array(neededBytes);
    let filled = 0;
    let h = sha256Bytes(utf8Bytes(password));
    while (filled < neededBytes) {
      const take = Math.min(32, neededBytes - filled);
      out.set(h.subarray(0, take), filled);
      filled += take;
      if (filled >= neededBytes) break;
      h = sha256Bytes(h);
    }
    return out;
  }

// 管理部16bitからアプリ暗号化フラグ（8ビット目）を正確に判定する
  function isAppEncryptionOnFromFirstQR(firstText){
    if (!firstText || firstText.length < 2) return false;

    // パターンA: 16文字の "0" / "1" 文字列として付与されている場合
    if (/^[01]{16}/.test(firstText)) {
      // 8文字目（インデックス7）が '1' ならアプリ暗号化ON
      return firstText.charAt(7) === '1';
    }

    // パターンB: 2バイトのバイナリ制御文字として付与されている場合
    // 0x01 (2進数:00000001) とAND演算して、8ビット目が 1 かどうかを判定
    const byte0 = firstText.charCodeAt(0);
    return (byte0 & 0x01) !== 0;
  }

  // =========================
  // QRの中間処理（①〜⑥）
  // =========================

  // フォーマット情報（15bit×2）を BitMatrix から読み出す
  function readFormatBits(bitMatrix) {
    const dim = bitMatrix.getWidth();

    // ZXing(BitMatrixParser) と同じ読み方の並び
    // 1) around top-left
    let bits1 = 0;
    // (0,8)〜(5,8)
    for (let i = 0; i <= 5; i++) bits1 = (bits1 << 1) | (bitMatrix.get(i, 8) ? 1 : 0);
    // (7,8)
    bits1 = (bits1 << 1) | (bitMatrix.get(7, 8) ? 1 : 0);
    // (8,8)
    bits1 = (bits1 << 1) | (bitMatrix.get(8, 8) ? 1 : 0);
    // (8,7)
    bits1 = (bits1 << 1) | (bitMatrix.get(8, 7) ? 1 : 0);
    // (8,5)〜(8,0)
    for (let j = 5; j >= 0; j--) bits1 = (bits1 << 1) | (bitMatrix.get(8, j) ? 1 : 0);

    // 2) the other copy (top-right / bottom-left)
    let bits2 = 0;
    // (dim-1,8)〜(dim-8,8)
    for (let i = dim - 1; i >= dim - 8; i--) bits2 = (bits2 << 1) | (bitMatrix.get(i, 8) ? 1 : 0);
    // (8, dim-7)〜(8, dim-1)
    for (let j = dim - 7; j < dim; j++) bits2 = (bits2 << 1) | (bitMatrix.get(8, j) ? 1 : 0);

    return { bits1, bits2 };
  }

  // データコード語列（totalCodewords 個）を BitMatrix から抽出（マスク解除後）
  function readCodewordsFromBitMatrix(unmaskedMatrix, version) {
    const dim = unmaskedMatrix.getWidth();
    const functionPattern = version.buildFunctionPattern(); // BitMatrix
    const totalCodewords = version.getTotalCodewords();

    const result = new Uint8Array(totalCodewords);
    let resultOffset = 0;
    let currentByte = 0;
    let bitsRead = 0;

    let readingUp = true;
    for (let col = dim - 1; col > 0; col -= 2) {
      if (col === 6) col--; // timing pattern col
      for (let rowIter = 0; rowIter < dim; rowIter++) {
        const row = readingUp ? (dim - 1 - rowIter) : rowIter;

        for (let c = 0; c < 2; c++) {
          const x = col - c;
          const y = row;

          if (functionPattern.get(x, y)) continue; // skip function modules

          currentByte = (currentByte << 1) | (unmaskedMatrix.get(x, y) ? 1 : 0);
          bitsRead++;

          if (bitsRead === 8) {
            if (resultOffset >= totalCodewords) {
              // 余分に読むことは通常ないが、安全のため break
              return result;
            }
            result[resultOffset++] = currentByte & 0xff;
            bitsRead = 0;
            currentByte = 0;
          }
        }
      }
      readingUp = !readingUp;
    }

    return result;
  }

  // RS復号（ブロック分割→各ブロックをReedSolomonDecoderで復号→データ部連結）
  function rsDecodeToDataBytes(allCodewords, version, ecLevel) {
    const ecBlocks = version.getECBlocksForLevel(ecLevel);
    const ecBlockArray = ecBlocks.getECBlocks(); // ECBlock[]
    const numBlocks = ecBlocks.getNumBlocks();

    // 各ブロックの構成を作る
    const blocks = [];
    for (let i = 0; i < ecBlockArray.length; i++) {
      const ecBlock = ecBlockArray[i];
      const count = ecBlock.getCount();
      const dataCodewords = ecBlock.getDataCodewords();
      for (let j = 0; j < count; j++) {
        blocks.push({ dataCodewords, codewords: null });
      }
    }

    const totalCodewords = version.getTotalCodewords();
    const ecCodewordsPerBlock = ecBlocks.getECCodewordsPerBlock();

    // 1ブロック当たりの最大 data codewords を求める（短いブロック/長いブロックが混在し得る）
    let maxDataLen = 0;
    for (const b of blocks) maxDataLen = Math.max(maxDataLen, b.dataCodewords);

    // Codewords をインターリーブ解除しながら blocks に詰める
    for (const b of blocks) {
      b.codewords = new Uint8Array(b.dataCodewords + ecCodewordsPerBlock);
    }

    let offset = 0;

    // data codewords (短いブロックと長いブロックで段階が分かれる)
    for (let i = 0; i < maxDataLen; i++) {
      for (let b = 0; b < blocks.length; b++) {
        if (i < blocks[b].dataCodewords) {
          blocks[b].codewords[i] = allCodewords[offset++];
        }
      }
    }

    // ec codewords
    for (let i = 0; i < ecCodewordsPerBlock; i++) {
      for (let b = 0; b < blocks.length; b++) {
        const idx = blocks[b].dataCodewords + i;
        blocks[b].codewords[idx] = allCodewords[offset++];
      }
    }

    if (offset !== totalCodewords) {
      throw new Error(`codeword read mismatch: read=${offset}, total=${totalCodewords}`);
    }

    // 各ブロックを RS 復号し、データ部を連結
    const rs = new ZXing.ReedSolomonDecoder(ZXing.GenericGF.QR_CODE_FIELD_256);
    const dataOut = [];

    for (const b of blocks) {
      const ints = new Int32Array(b.codewords.length);
      for (let i = 0; i < b.codewords.length; i++) ints[i] = b.codewords[i] & 0xff;

      // decode(ints, numEcCodewords)
      rs.decode(ints, ecCodewordsPerBlock);

      // data 部だけ取り出す（先頭 dataCodewords）
      for (let i = 0; i < b.dataCodewords; i++) dataOut.push(ints[i] & 0xff);
    }

    return new Uint8Array(dataOut);
  }

  async function decryptSecondFromFrame(video, password){
    if (!window.ZXing) throw new Error("ZXing が見つかりません。zxing.min.js の読み込みを確認してください。");
    if (!video) throw new Error("decryptSecondFromFrame: video が渡されていません。");

    // ① 検出→サンプリング→BitMatrix化（BinaryBitmap→BlackMatrix）
    const reader = new ZXing.BrowserQRCodeReader();
    const binaryBitmap = reader.createBinaryBitmap(video);
    const matrix = binaryBitmap.getBlackMatrix(); // BitMatrix

    // ② フォーマット情報からマスク番号取得
    const { bits1, bits2 } = readFormatBits(matrix);
    const fmt = ZXing.QRCodeDecoderFormatInformation.decodeFormatInformation(bits1, bits2);
    if (!fmt) throw new Error("FormatInformation の復元に失敗しました。");

    const maskPattern = fmt.getDataMask();
    const ecLevel = fmt.getErrorCorrectionLevel();

    // version は Dimension から推定（dimension = 17 + 4*version）
    const dim = matrix.getWidth();
    const versionNum = (dim - 17) / 4;
    const version = ZXing.QRCodeVersion.getVersionForNumber(versionNum);

    // ③ マスク解除してコード語列抽出
    // ※DataMask は matrix を in-place で unmask する想定
    const unmasked = matrix.clone();
    ZXing.QRCodeDataMask.forReference(maskPattern).unmaskBitMatrix(unmasked, dim);

    const codewords = readCodewordsFromBitMatrix(unmasked, version); // 全コード語（データ+ECC）

    // ④ 全コード語に対して、パスワード由来マスクでXORして戻す
    const mask = deriveMask(password ?? "", codewords.length);
    const xored = new Uint8Array(codewords.length);
    for (let i = 0; i < codewords.length; i++) xored[i] = (codewords[i] ^ mask[i]) & 0xff;

    // ⑤ RS復号（誤り訂正）
    const dataBytes = rsDecodeToDataBytes(xored, version, ecLevel);

    // ⑥ ふつうにデータ解釈（Byte/Kanji等）
    const decoderResult = ZXing.QRCodeDecodedBitStreamParser.decode(dataBytes, version, ecLevel, null);
    return decoderResult.getText();
  }

  return { deriveMask, isAppEncryptionOnFromFirstQR, decryptSecondFromFrame };

})();




