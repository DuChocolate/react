/**
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * @flow
 */

/**
 * HTML nodeType values that represent the type of the node
 */

export const ELEMENT_NODE = 1;    //代表元素
export const TEXT_NODE = 3;   //代表元素或属性中的文本内容
export const COMMENT_NODE = 8;   //代表注释
export const DOCUMENT_NODE = 9;   //代表整个文档（DOM树的根节点）
export const DOCUMENT_FRAGMENT_NODE = 11;    //代表轻量级的 Document 对象，能够容纳文档的某个部分
